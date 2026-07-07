// ============================================================
// Poker server — authoritative Texas Hold'em relay.
//
// Unlike the Othello/Dots relay (which just forwarded messages
// between 2 peers), this server OWNS the game state: it shuffles
// the deck, deals hole cards privately to each player, runs the
// betting rounds, and computes showdowns. That is what makes
// hidden cards actually hidden — a player is only ever sent their
// own two cards.
//
// Protocol (client -> server):
//   { type:'join', code, name }        join/create a room
//   { type:'sit' }                     take a seat (before hand)
//   { type:'start' }                   host starts the hand
//   { type:'action', action, amount }  fold|check|call|bet|raise, amount = "raise to" total
//   { type:'next' }                    host deals the next hand
//   { type:'chat', text }
//
// Protocol (server -> client):
//   { type:'joined', you, host }       your seat id + whether you host
//   { type:'state', pub, you }         redacted public state + your private cards
//   { type:'chat', name, text }
//   { type:'error', text }
//
// Deploy exactly like the othello relay (Render / Railway / Fly, a
// node process exposing $PORT). Point the client SERVER_URL at it.
// ============================================================

const http = require('http');
const { WebSocketServer } = require('ws');
const PORT = process.env.PORT || 8080;

const SUITS = 4, RANKS = 13; // rank 0..12 -> 2..A
function makeDeck() {
    const d = [];
    for (let s = 0; s < SUITS; s++) for (let r = 0; r < RANKS; r++) d.push(r * 4 + s);
    for (let i = d.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [d[i], d[j]] = [d[j], d[i]];
    }
    return d;
}
const cardRank = c => (c / 4) | 0;      // 0..12
const cardSuit = c => c % 4;            // 0..3

// ---- 5-of-7 hand evaluation -> comparable array [cat, ...tiebreak] ----
function eval5(cards) {
    const rs = cards.map(cardRank).sort((a, b) => b - a);
    const suits = cards.map(cardSuit);
    const flush = suits.every(s => s === suits[0]);
    const uniq = [...new Set(rs)];
    let straightHigh = 0;
    if (uniq.length === 5) {
        if (uniq[0] - uniq[4] === 4) straightHigh = uniq[0];
        else if (uniq[0] === 12 && uniq[1] === 3 && uniq[4] === 0) straightHigh = 3; // wheel A-5-4-3-2
    }
    const cnt = {};
    for (const r of rs) cnt[r] = (cnt[r] || 0) + 1;
    const groups = Object.entries(cnt).map(([r, c]) => [c, +r]).sort((a, b) => b[0] - a[0] || b[1] - a[1]);
    const counts = groups.map(g => g[0]);
    let cat;
    if (straightHigh && flush) cat = 8;
    else if (counts[0] === 4) cat = 7;
    else if (counts[0] === 3 && counts[1] === 2) cat = 6;
    else if (flush) cat = 5;
    else if (straightHigh) cat = 4;
    else if (counts[0] === 3) cat = 3;
    else if (counts[0] === 2 && counts[1] === 2) cat = 2;
    else if (counts[0] === 2) cat = 1;
    else cat = 0;
    let tie;
    if (cat === 8 || cat === 4) tie = [straightHigh];
    else if (cat === 5 || cat === 0) tie = rs;
    else tie = groups.map(g => g[1]);
    return [cat, ...tie];
}
function cmpScore(a, b) {
    for (let i = 0; i < Math.max(a.length, b.length); i++) {
        const x = a[i] || 0, y = b[i] || 0;
        if (x !== y) return x - y;
    }
    return 0;
}
const COMBOS5 = (() => {
    const out = [];
    for (let a = 0; a < 3; a++) for (let b = a + 1; b < 4; b++) for (let c = b + 1; c < 5; c++)
        for (let d = c + 1; d < 6; d++) for (let e = d + 1; e < 7; e++) out.push([a, b, c, d, e]);
    return out;
})();
function best7(cards7) {
    let best = null;
    for (const combo of COMBOS5) {
        const sc = eval5(combo.map(i => cards7[i]));
        if (!best || cmpScore(sc, best) > 0) best = sc;
    }
    return best;
}
const CAT_NAMES = ['High card', 'Pair', 'Two pair', 'Three of a kind', 'Straight',
    'Flush', 'Full house', 'Four of a kind', 'Straight flush'];
function handName(score) {
    if (score[0] === 8 && score[1] === 12) return 'Royal flush';
    return CAT_NAMES[score[0]];
}

// ============================================================
// Room / game state
// ============================================================
const rooms = new Map();

function newRoom(code) {
    return {
        code,
        players: [],          // { id, ws, name, seat, stack, sittingOut }
        nextSeat: 0,
        hostId: null,
        started: false,
        // hand state:
        inHand: false,
        deck: [], community: [],
        hole: {},             // seat -> [c,c]
        inHandSeats: [],      // seats dealt this hand
        folded: {}, allIn: {},
        bet: {},              // committed this street, by seat
        paid: {},             // committed this hand, by seat
        stacks: {},           // working stacks during hand, by seat
        pot: 0,
        street: 'idle',       // idle|preflop|flop|turn|river|showdown
        toAct: null,
        button: -1,
        sb: 1, bb: 2, startStack: 200,
        minRaise: 2,
        numActed: 0,
        lastAggressor: null,
        log: [],
        result: null,
    };
}

function activePlayers(room) { return room.players.filter(p => !p.sittingOut && p.stack > 0); }
function seatPlayer(room, seat) { return room.players.find(p => p.seat === seat); }
function log(room, line) { room.log.push(line); if (room.log.length > 40) room.log.shift(); }

function startHand(room) {
    const seated = room.players.filter(p => !p.sittingOut && p.stack > 0);
    if (seated.length < 2) { room.log.push('Need at least 2 players with chips.'); broadcast(room); return; }

    room.inHand = true;
    room.deck = makeDeck();
    room.community = [];
    room.hole = {};
    room.folded = {}; room.allIn = {}; room.bet = {}; room.paid = {}; room.stacks = {};
    room.pot = 0;
    room.result = null;
    room.street = 'preflop';
    room.minRaise = room.bb;
    room.numActed = 0;

    const seats = seated.map(p => p.seat).sort((a, b) => a - b);
    room.inHandSeats = seats;

    // advance button to next seated player
    let bi = seats.indexOf(room.button);
    room.button = seats[(bi + 1) % seats.length];
    if (bi === -1) room.button = seats[0];

    for (const s of seats) {
        room.stacks[s] = seatPlayer(room, s).stack;
        room.bet[s] = 0; room.paid[s] = 0; room.folded[s] = false; room.allIn[s] = false;
        room.hole[s] = [room.deck.pop(), room.deck.pop()];
    }

    // blinds
    const order = rotate(seats, seats.indexOf(room.button));
    let sbSeat, bbSeat, firstToAct;
    if (seats.length === 2) {
        // heads-up: button is small blind, acts first preflop
        sbSeat = room.button;
        bbSeat = order[1];
        firstToAct = sbSeat;
    } else {
        sbSeat = order[1];
        bbSeat = order[2];
        firstToAct = order[3 % seats.length];
    }
    postBlind(room, sbSeat, room.sb);
    postBlind(room, bbSeat, room.bb);
    room.lastAggressor = bbSeat;   // BB has option preflop
    room.toAct = nextAbleFrom(room, firstToAct, true);

    log(room, `— New hand. Blinds ${room.sb}/${room.bb}. ${seatPlayer(room, bbSeat).name} posts big blind.`);
    broadcast(room);
    maybeAutoAdvance(room);
}

function rotate(arr, startIdx) { return arr.slice(startIdx).concat(arr.slice(0, startIdx)); }
function postBlind(room, seat, amt) {
    const put = Math.min(amt, room.stacks[seat]);
    room.stacks[seat] -= put; room.bet[seat] += put; room.paid[seat] += put;
    if (room.stacks[seat] === 0) room.allIn[seat] = true;
}
function curBet(room) { return Math.max(0, ...room.inHandSeats.map(s => room.bet[s])); }
function ableSeats(room) { return room.inHandSeats.filter(s => !room.folded[s] && !room.allIn[s]); }
function liveSeats(room) { return room.inHandSeats.filter(s => !room.folded[s]); }

function nextAbleFrom(room, seat, inclusive) {
    const seats = room.inHandSeats;
    let idx = seats.indexOf(seat);
    if (idx === -1) idx = 0;
    for (let k = 0; k < seats.length; k++) {
        const s = seats[(idx + (inclusive && k === 0 ? 0 : k)) % seats.length];
        if (!room.folded[s] && !room.allIn[s]) return s;
        if (k === 0 && inclusive) continue;
    }
    // fallback linear scan
    for (let k = inclusive ? 0 : 1; k < seats.length + 1; k++) {
        const s = seats[(idx + k) % seats.length];
        if (!room.folded[s] && !room.allIn[s]) return s;
    }
    return null;
}
function seatAfter(room, seat) {
    const seats = room.inHandSeats;
    let idx = seats.indexOf(seat);
    for (let k = 1; k <= seats.length; k++) {
        const s = seats[(idx + k) % seats.length];
        if (!room.folded[s] && !room.allIn[s]) return s;
    }
    return null;
}

function applyAction(room, seat, action, amount) {
    if (!room.inHand || seat !== room.toAct) return;
    const cb = curBet(room);
    const p = seatPlayer(room, seat);

    if (action === 'fold') {
        room.folded[seat] = true;
        log(room, `${p.name} folds.`);
        if (liveSeats(room).length === 1) return endByFold(room);
    } else if (action === 'check') {
        if (cb - room.bet[seat] !== 0) return;
        room.numActed++;
        log(room, `${p.name} checks.`);
    } else if (action === 'call') {
        const need = cb - room.bet[seat];
        const put = Math.min(need, room.stacks[seat]);
        commit(room, seat, put);
        room.numActed++;
        log(room, `${p.name} calls ${put}.`);
    } else if (action === 'bet' || action === 'raise') {
        const maxTo = room.bet[seat] + room.stacks[seat];
        const minTo = cb === 0 ? Math.min(room.bb, maxTo) : Math.min(cb + room.minRaise, maxTo);
        let target = Math.max(minTo, Math.min(amount | 0, maxTo));
        const raiseSize = target - cb;
        const put = target - room.bet[seat];
        commit(room, seat, put);
        if (raiseSize > 0) {
            room.minRaise = Math.max(room.minRaise, raiseSize);
            room.lastAggressor = seat;
            room.numActed = 1;
            log(room, `${p.name} ${cb === 0 ? 'bets' : 'raises to'} ${target}.`);
        } else {
            room.numActed++;
            log(room, `${p.name} calls ${put} (all-in).`);
        }
    } else return;

    advanceOrClose(room, seat);
}

function commit(room, seat, put) {
    room.stacks[seat] -= put; room.bet[seat] += put; room.paid[seat] += put;
    if (room.stacks[seat] === 0) room.allIn[seat] = true;
}

function advanceOrClose(room, seat) {
    const cb = curBet(room);
    const able = ableSeats(room);
    const allMatched = able.every(s => room.bet[s] === cb);

    if (able.length === 0) return runoutAndShowdown(room);
    if (able.length === 1) {
        const q = able[0];
        if (room.bet[q] >= cb && room.numActed >= 1) return closeStreet(room);
        room.toAct = q; broadcast(room); maybeAutoAdvance(room); return;
    }
    if (allMatched && room.numActed >= able.length) return closeStreet(room);
    room.toAct = seatAfter(room, seat);
    broadcast(room);
    maybeAutoAdvance(room);
}

function closeStreet(room) {
    for (const s of room.inHandSeats) { room.pot += room.bet[s]; room.bet[s] = 0; }
    room.numActed = 0; room.minRaise = room.bb; room.lastAggressor = null;

    if (ableSeats(room).length < 2) return runoutAndShowdown(room);

    if (room.street === 'preflop') { deal(room, 3); room.street = 'flop'; }
    else if (room.street === 'flop') { deal(room, 1); room.street = 'turn'; }
    else if (room.street === 'turn') { deal(room, 1); room.street = 'river'; }
    else if (room.street === 'river') return showdown(room);

    log(room, `— ${room.street[0].toUpperCase() + room.street.slice(1)}.`);
    // first to act after button (post-flop): next live seat clockwise from button
    room.toAct = seatAfter(room, room.button) ?? liveSeats(room)[0];
    broadcast(room);
    maybeAutoAdvance(room);
}

function deal(room, n) { for (let i = 0; i < n; i++) room.community.push(room.deck.pop()); }

function runoutAndShowdown(room) {
    for (const s of room.inHandSeats) { room.pot += room.bet[s]; room.bet[s] = 0; }
    while (room.community.length < 5) room.community.push(room.deck.pop());
    showdown(room);
}

function endByFold(room) {
    for (const s of room.inHandSeats) { room.pot += room.bet[s]; room.bet[s] = 0; }
    const winner = liveSeats(room)[0];
    const w = seatPlayer(room, winner);
    w.stack = room.stacks[winner] + room.pot;
    room.result = { winners: [winner], reveal: false, byFold: true, potWon: room.pot, hands: {} };
    log(room, `${w.name} wins ${room.pot} (everyone folded).`);
    endHand(room);
}

function showdown(room) {
    const contenders = liveSeats(room);
    // build side pots from paid[]
    const pots = buildPots(room, contenders);
    const scores = {};
    for (const s of contenders) scores[s] = best7(room.hole[s].concat(room.community));

    const awarded = {};
    const winnersSet = new Set();
    for (const pot of pots) {
        let best = null, winners = [];
        for (const s of pot.eligible) {
            if (!(s in scores)) continue;
            const c = best ? cmpScore(scores[s], best) : 1;
            if (!best || c > 0) { best = scores[s]; winners = [s]; }
            else if (c === 0) winners.push(s);
        }
        const share = Math.floor(pot.amount / winners.length);
        let rem = pot.amount - share * winners.length;
        for (const w of winners) { awarded[w] = (awarded[w] || 0) + share + (rem-- > 0 ? 1 : 0); winnersSet.add(w); }
    }
    for (const s of room.inHandSeats) {
        seatPlayer(room, s).stack = room.stacks[s] + (awarded[s] || 0);
    }
    const hands = {};
    for (const s of contenders) hands[s] = { cards: room.hole[s], name: handName(scores[s]) };
    room.result = { winners: [...winnersSet], reveal: true, byFold: false, awarded, hands };
    for (const w of winnersSet) log(room, `${seatPlayer(room, w).name} wins ${awarded[w]} — ${hands[w].name}.`);
    endHand(room);
}

// side pots based on total paid[] this hand
function buildPots(room, contenders) {
    const contribs = room.inHandSeats.map(s => ({ s, paid: room.paid[s], live: !room.folded[s] }));
    const levels = [...new Set(contribs.filter(c => c.paid > 0).map(c => c.paid))].sort((a, b) => a - b);
    const pots = [];
    let prev = 0;
    for (const lvl of levels) {
        let amount = 0;
        const eligible = [];
        for (const c of contribs) {
            const in_ = Math.max(0, Math.min(c.paid, lvl) - prev);
            amount += in_;
            if (c.paid >= lvl && c.live) eligible.push(c.s);
        }
        if (amount > 0) pots.push({ amount, eligible });
        prev = lvl;
    }
    return pots;
}

function endHand(room) {
    room.inHand = false;
    room.street = 'showdown';
    room.toAct = null;
    broadcast(room);
}

function maybeAutoAdvance() { /* server does not act for players */ }

// ============================================================
// Views: redact so each player only sees their own hole cards.
// ============================================================
function publicState(room) {
    const cb = curBet(room);
    return {
        code: room.code,
        started: room.started,
        inHand: room.inHand,
        street: room.street,
        community: room.community.slice(),
        pot: room.pot,
        streetBets: Object.fromEntries(room.inHandSeats.map(s => [s, room.bet[s]])),
        curBet: cb,
        toAct: room.toAct,
        button: room.button,
        sb: room.sb, bb: room.bb, minRaise: room.minRaise,
        hostId: room.hostId,
        result: room.result,
        log: room.log.slice(-8),
        players: room.players.map(p => ({
            id: p.id, name: p.name, seat: p.seat, stack: p.stack,
            sittingOut: p.sittingOut,
            inHand: room.inHand && room.inHandSeats.includes(p.seat),
            folded: room.inHand ? !!room.folded[p.seat] : false,
            allIn: room.inHand ? !!room.allIn[p.seat] : false,
            // reveal hole cards only at showdown for players still live
            revealed: (room.result && room.result.reveal && room.result.hands[p.seat])
                ? room.result.hands[p.seat].cards : null,
        })),
    };
}
function privateFor(room, player) {
    if (room.inHand && room.hole[player.seat] && !room.folded[player.seat]) {
        return { hole: room.hole[player.seat], seat: player.seat };
    }
    if (room.inHand && room.hole[player.seat]) return { hole: room.hole[player.seat], seat: player.seat };
    return { hole: null, seat: player.seat };
}
function broadcast(room) {
    const pub = publicState(room);
    for (const p of room.players) {
        if (p.ws.readyState !== 1) continue;
        p.ws.send(JSON.stringify({ type: 'state', pub, you: privateFor(room, p) }));
    }
}

// ============================================================
// WebSocket wiring
// ============================================================
const server = http.createServer((req, res) => {
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    res.end('Poker server running');
});
const wss = new WebSocketServer({ server });

wss.on('connection', (ws) => {
    ws.roomCode = null; ws.pid = null;

    ws.on('message', (raw) => {
        let m; try { m = JSON.parse(raw); } catch { return; }
        const room = ws.roomCode ? rooms.get(ws.roomCode) : null;

        if (m.type === 'join') {
            const code = String(m.code || '').toUpperCase().slice(0, 8);
            if (!code) return;
            if (!rooms.has(code)) rooms.set(code, newRoom(code));
            const r = rooms.get(code);
            if (r.players.length >= 9) { ws.send(JSON.stringify({ type: 'error', text: 'Table full (9 max).' })); return; }
            const id = Math.random().toString(36).slice(2, 8);
            const player = {
                id, ws, name: (m.name || 'Player').slice(0, 14),
                seat: r.nextSeat++, stack: r.startStack, sittingOut: false,
            };
            r.players.push(player);
            if (!r.hostId) r.hostId = id;
            ws.roomCode = code; ws.pid = id;
            ws.send(JSON.stringify({ type: 'joined', you: id, host: r.hostId === id, seat: player.seat }));
            log(r, `${player.name} joined.`);
            broadcast(r);
            return;
        }
        if (!room) return;
        const me = room.players.find(p => p.id === ws.pid);
        if (!me) return;

        if (m.type === 'config' && room.hostId === me.id && !room.inHand) {
            if (m.startStack) room.startStack = Math.max(20, m.startStack | 0);
            if (m.sb) { room.sb = Math.max(1, m.sb | 0); room.bb = room.sb * 2; }
            broadcast(room);
        } else if (m.type === 'start' && room.hostId === me.id && !room.inHand) {
            room.started = true;
            startHand(room);
        } else if (m.type === 'next' && room.hostId === me.id && !room.inHand) {
            startHand(room);
        } else if (m.type === 'action') {
            applyAction(room, me.seat, m.action, m.amount);
        } else if (m.type === 'sitout') {
            me.sittingOut = !!m.value; broadcast(room);
        } else if (m.type === 'chat') {
            const text = String(m.text || '').slice(0, 200);
            for (const p of room.players) if (p.ws.readyState === 1)
                p.ws.send(JSON.stringify({ type: 'chat', name: me.name, text }));
        }
    });

    ws.on('close', () => {
        const room = ws.roomCode ? rooms.get(ws.roomCode) : null;
        if (!room) return;
        const idx = room.players.findIndex(p => p.id === ws.pid);
        if (idx === -1) return;
        const gone = room.players[idx];
        log(room, `${gone.name} left.`);
        // if in a hand, fold them
        if (room.inHand && room.inHandSeats.includes(gone.seat) && !room.folded[gone.seat]) {
            room.folded[gone.seat] = true;
            if (room.toAct === gone.seat) advanceOrClose(room, gone.seat);
            if (liveSeats(room).length === 1 && room.inHand) endByFold(room);
        }
        room.players.splice(idx, 1);
        if (room.hostId === gone.id && room.players.length) room.hostId = room.players[0].id;
        if (room.players.length === 0) rooms.delete(room.code);
        else broadcast(room);
    });
});

server.listen(PORT, () => console.log('Poker server listening on ' + PORT));
