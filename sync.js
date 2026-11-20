/**
 * P-Near Hybrid Serverless Sync Engine
 * - Transport 1: WebRTC Peer-to-Peer DataChannel (PeerJS + Google/Cloudflare STUN)
 * - Transport 2: End-to-End Encrypted Multi-Relay Nostr Mesh (TLS port 443 WSS)
 *   - Uses kind 20000 (ephemeral low-latency updates)
 *   - Uses kind 30078 (replaceable snapshot for instant mid-trip / reconnect sync)
 *   - Uses kind 20001 (encrypted viewer presence pings over relay fallback)
 * - Deterministic secp256k1 + BIP-340 Schnorr keys derived purely from URL #key (never exposed to relays)
 */
(function (global) {
    'use strict';

    const ICE_SERVERS = [
        { urls: 'stun:stun.l.google.com:19302' },
        { urls: 'stun:stun1.l.google.com:19302' },
        { urls: 'stun:stun2.l.google.com:19302' },
        { urls: 'stun:stun.cloudflare.com:3478' }
    ];

    const PEER_CONFIG = {
        config: {
            iceServers: ICE_SERVERS,
            iceCandidatePoolSize: 4,
            sdpSemantics: 'unified-plan'
        },
        debug: 1
    };

    // Empirically verified public TLS port-443 Nostr relays supporting ephemeral + replaceable events
    const NOSTR_RELAYS = [
        'wss://relay.snort.social',
        'wss://relay.primal.net',
        'wss://nostr.oxtr.dev',
        'wss://offchain.pub'
    ];

    // --- PURE BIGINT SECP256K1 + BIP-340 SCHNORR ---
    const P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2Fn;
    const N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
    const Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
    const Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;

    function mod(a, m) {
        return ((a % m) + m) % m;
    }

    function powMod(base, exp, m) {
        let res = 1n;
        base = mod(base, m);
        while (exp > 0n) {
            if (exp & 1n) res = (res * base) % m;
            base = (base * base) % m;
            exp >>= 1n;
        }
        return res;
    }

    function invMod(a, m) {
        return powMod(a, m - 2n, m);
    }

    function pointAdd(p1, p2) {
        if (!p1) return p2;
        if (!p2) return p1;
        const [x1, y1] = p1;
        const [x2, y2] = p2;
        if (x1 === x2) {
            if (y1 !== y2) return null;
            const lam = mod(3n * x1 * x1 * invMod(2n * y1, P), P);
            const x3 = mod(lam * lam - 2n * x1, P);
            return [x3, mod(lam * (x1 - x3) - y1, P)];
        }
        const lam = mod((y2 - y1) * invMod(x2 - x1, P), P);
        const x3 = mod(lam * lam - x1 - x2, P);
        return [x3, mod(lam * (x1 - x3) - y1, P)];
    }

    function pointMul(k, pt) {
        let r = null;
        let a = pt || [Gx, Gy];
        let rem = k;
        while (rem > 0n) {
            if (rem & 1n) r = pointAdd(r, a);
            a = pointAdd(a, a);
            rem >>= 1n;
        }
        return r;
    }

    function getCryptoJS() {
        const lib = (typeof global !== 'undefined' && global.CryptoJS) || (typeof CryptoJS !== 'undefined' ? CryptoJS : null);
        if (!lib) throw new Error('CryptoJS is required for P-Near sync encryption.');
        return lib;
    }

    function sha256HexUtf8(str) {
        const CJS = getCryptoJS();
        return CJS.SHA256(str).toString(CJS.enc.Hex);
    }

    function sha256HexFromHex(hexStr) {
        const CJS = getCryptoJS();
        const wa = CJS.enc.Hex.parse(hexStr);
        return CJS.SHA256(wa).toString(CJS.enc.Hex);
    }

    function asciiToHex(str) {
        let out = '';
        for (let i = 0; i < str.length; i++) {
            out += str.charCodeAt(i).toString(16).padStart(2, '0');
        }
        return out;
    }

    function numToHex32(num) {
        return num.toString(16).padStart(64, '0');
    }

    function xorHex32(aHex, bHex) {
        const res = BigInt('0x' + aHex) ^ BigInt('0x' + bHex);
        return numToHex32(res);
    }

    function taggedHashHex(tag, msgHex) {
        const tagHashHex = sha256HexFromHex(asciiToHex(tag));
        return sha256HexFromHex(tagHashHex + tagHashHex + msgHex);
    }

    function randomHex32() {
        if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
            const arr = new Uint8Array(32);
            crypto.getRandomValues(arr);
            return Array.from(arr, b => b.toString(16).padStart(2, '0')).join('');
        }
        const CJS = getCryptoJS();
        return CJS.lib.WordArray.random(32).toString(CJS.enc.Hex);
    }

    function deriveChannelIdentity(cID, secretKey, role) {
        const seedHex = sha256HexUtf8(`pnear-v2:${role}:${cID}:${secretKey}`);
        let d = BigInt('0x' + seedHex) % (N - 1n);
        if (d === 0n) d = 1n;
        const privHex = numToHex32(d);
        const pubPt = pointMul(d);
        const pubHex = numToHex32(pubPt[0]);
        const dTag = sha256HexUtf8(`pnear-v2:dtag:${cID}:${secretKey}`).slice(0, 24);
        return { privHex, pubHex, dTag };
    }

    function signNostrEvent(kind, tags, content, identity, customCreatedAt) {
        const created_at = Number.isFinite(customCreatedAt) ? customCreatedAt : Math.floor(Date.now() / 1000);
        const serialized = JSON.stringify([0, identity.pubHex, created_at, kind, tags, content]);
        const id = sha256HexUtf8(serialized);

        let d = BigInt('0x' + identity.privHex);
        const Ppt = pointMul(d);
        if ((Ppt[1] & 1n) !== 0n) d = N - d;

        const pxHex = numToHex32(Ppt[0]);
        const auxHex = randomHex32();
        const tHex = xorHex32(numToHex32(d), taggedHashHex('BIP0340/aux', auxHex));
        const randHex = taggedHashHex('BIP0340/nonce', tHex + pxHex + id);
        let k = mod(BigInt('0x' + randHex), N);
        if (k === 0n) k = 1n;

        const R = pointMul(k);
        if ((R[1] & 1n) !== 0n) k = N - k;

        const rxHex = numToHex32(R[0]);
        const eHex = taggedHashHex('BIP0340/challenge', rxHex + pxHex + id);
        const e = mod(BigInt('0x' + eHex), N);
        const s = mod(k + e * d, N);
        const sig = rxHex + numToHex32(s);

        return { id, pubkey: identity.pubHex, created_at, kind, tags, content, sig };
    }

    function encryptPacket(packet, secretKey) {
        const CJS = getCryptoJS();
        return CJS.AES.encrypt(JSON.stringify(packet), secretKey).toString();
    }

    function decryptPacket(ciphertext, secretKey, expectedCID) {
        try {
            const CJS = getCryptoJS();
            const decryptedStr = CJS.AES.decrypt(ciphertext, secretKey).toString(CJS.enc.Utf8);
            if (!decryptedStr) return null;
            const parsed = JSON.parse(decryptedStr);
            if (!parsed || typeof parsed !== 'object') return null;
            if (expectedCID && parsed.cID && parsed.cID !== expectedCID) return null;
            return parsed;
        } catch {
            return null;
        }
    }

    /**
     * Resilient WebSocket pool across multiple independent Nostr relays with auto-reconnect.
     */
    class NostrRelayMesh {
        constructor(relays, options) {
            this.relays = relays || NOSTR_RELAYS;
            this.options = options || {};
            this.sockets = new Map();
            this.subs = []; // Array of { subId, filters, onEvent }
            this.pendingEvents = [];
            this.latestSnapshotFrame = null;
            this.destroyed = false;
            this.backoff = new Map();
            this.reconnectTimers = new Map();
            this.seenIds = new Set();
        }

        connect() {
            this.destroyed = false;
            this.relays.forEach((url) => this._connectRelay(url));
        }

        ensureConnected() {
            if (this.destroyed) return;
            this.relays.forEach((url) => {
                const ws = this.sockets.get(url);
                if (!ws || ws.readyState === 2 || ws.readyState === 3) {
                    this.backoff.set(url, 2000);
                    this._connectRelay(url);
                }
            });
        }

        destroy() {
            this.destroyed = true;
            this.reconnectTimers.forEach((t) => clearTimeout(t));
            this.reconnectTimers.clear();
            this.sockets.forEach((ws) => {
                try { ws.close(); } catch { /* ignore */ }
            });
            this.sockets.clear();
            this.subs = [];
            this.pendingEvents = [];
            this.latestSnapshotFrame = null;
            this.seenIds.clear();
        }

        getOpenCount() {
            let count = 0;
            this.sockets.forEach((ws) => {
                if (ws && ws.readyState === 1) count++;
            });
            return count;
        }

        subscribe(subId, filters, onEvent) {
            this.subs = this.subs.filter(s => s.subId !== subId);
            const entry = { subId, filters, onEvent };
            this.subs.push(entry);

            const reqFrame = JSON.stringify(['REQ', subId, ...filters]);
            this.sockets.forEach((ws) => {
                if (ws && ws.readyState === 1) {
                    try { ws.send(reqFrame); } catch { /* ignore */ }
                }
            });
        }

        publish(eventObj) {
            if (this.destroyed) return 0;
            const frame = JSON.stringify(['EVENT', eventObj]);
            if (eventObj && eventObj.kind === 30078) {
                this.latestSnapshotFrame = frame;
            }
            let sentCount = 0;

            this.sockets.forEach((ws) => {
                if (ws && ws.readyState === 1) {
                    try {
                        ws.send(frame);
                        sentCount++;
                    } catch { /* ignore */ }
                }
            });

            if (sentCount === 0 && (!eventObj || eventObj.kind !== 30078)) {
                this.pendingEvents.push(frame);
                if (this.pendingEvents.length > 5) {
                    this.pendingEvents.shift();
                }
            }
            return sentCount;
        }

        _connectRelay(url) {
            if (this.destroyed || typeof WebSocket === 'undefined') return;
            const existing = this.sockets.get(url);
            if (existing && (existing.readyState === 0 || existing.readyState === 1)) return;

            let ws;
            try {
                ws = new WebSocket(url);
            } catch {
                this._scheduleReconnect(url);
                return;
            }

            this.sockets.set(url, ws);

            ws.onopen = () => {
                if (this.destroyed) {
                    try { ws.close(); } catch { /* ignore */ }
                    return;
                }
                this.backoff.set(url, 2000);

                // Register active subscriptions
                this.subs.forEach((sub) => {
                    try {
                        ws.send(JSON.stringify(['REQ', sub.subId, ...sub.filters]));
                    } catch { /* ignore */ }
                });

                // Always push latest replaceable snapshot to each newly opened relay so all relays stay warm
                if (this.latestSnapshotFrame) {
                    try { ws.send(this.latestSnapshotFrame); } catch { /* ignore */ }
                }

                // Flush buffered ephemeral events until first relay connects
                while (this.pendingEvents.length > 0) {
                    const frame = this.pendingEvents[0];
                    try {
                        ws.send(frame);
                        this.pendingEvents.shift();
                    } catch {
                        break;
                    }
                }

                this._notifyHealth();
            };

            ws.onmessage = (msg) => {
                if (this.destroyed) return;
                try {
                    const data = JSON.parse(msg.data);
                    if (!Array.isArray(data)) return;

                    if (data[0] === 'EVENT' && data[2] && data[2].id) {
                        const subId = data[1];
                        const ev = data[2];
                        if (this.seenIds.has(ev.id)) return;
                        this.seenIds.add(ev.id);
                        if (this.seenIds.size > 400) {
                            const first = this.seenIds.values().next().value;
                            this.seenIds.delete(first);
                        }

                        const sub = this.subs.find(s => s.subId === subId);
                        if (sub && sub.onEvent) {
                            sub.onEvent(ev, url);
                        }
                    }
                } catch { /* ignore malformed relay frame */ }
            };

            ws.onclose = () => {
                if (!this.destroyed) {
                    this._notifyHealth();
                    this._scheduleReconnect(url);
                }
            };

            ws.onerror = () => {
                if (!this.destroyed) {
                    try { ws.close(); } catch { /* ignore */ }
                }
            };
        }

        _scheduleReconnect(url) {
            if (this.destroyed || this.reconnectTimers.has(url)) return;
            const delay = this.backoff.get(url) || 2000;
            this.backoff.set(url, Math.min(20000, Math.round(delay * 1.8)));
            const timer = setTimeout(() => {
                this.reconnectTimers.delete(url);
                this._connectRelay(url);
            }, delay);
            this.reconnectTimers.set(url, timer);
        }

        _notifyHealth() {
            if (this.options.onHealthChange) {
                this.options.onHealthChange(this.getOpenCount(), this.relays.length);
            }
        }
    }

    /**
     * Coordinates Dual-Transport delivery for Sharer or Viewer.
     */
    class HybridSessionManager {
        constructor(callbacks) {
            this.callbacks = callbacks || {};
            this.peer = null;
            this.relayMesh = null;
            this.mode = null; // 'sharer' | 'viewer'
            this.cID = null;
            this.key = null;
            this.sharerId = null;
            this.viewerId = null;
            this.viewerConns = new Set(); // WebRTC conns (sharer side)
            this.viewerConn = null;       // WebRTC conn (viewer side)
            this.relayViewers = new Map(); // vid -> lastSeenMs (sharer side)
            this.localViewerId = randomHex32().slice(0, 12);

            this.seq = 0;
            this.highestReceivedSeq = 0;
            this.lastSnapshotAtMs = 0;
            this.lastSnapshotSec = 0;
            this.lastEphAtMs = 0;
            this.viewerPresenceTimer = null;
            this.viewerReconnectTimer = null;
            this.peerWatchdogTimer = null;
            this.lastBroadcastPayload = null;
            this.destroyed = false;
        }

        _nextSeq() {
            const now = Date.now();
            this.seq = Math.max(this.seq + 1, now);
            return this.seq;
        }

        startSharer(shareSession) {
            this.stop();
            this.destroyed = false;
            this.mode = 'sharer';
            this.cID = shareSession.cID;
            this.key = shareSession.key;
            this.sharerId = deriveChannelIdentity(this.cID, this.key, 'sharer');
            this.viewerId = deriveChannelIdentity(this.cID, this.key, 'viewer');

            // 1. Start Nostr Multi-Relay Mesh immediately (TLS port 443, works everywhere)
            this.relayMesh = new NostrRelayMesh(NOSTR_RELAYS, {
                onHealthChange: () => this._emitStatus()
            });
            this.relayMesh.connect();
            this.relayMesh.subscribe('viewers', [
                { authors: [this.viewerId.pubHex], kinds: [20001], since: Math.floor(Date.now() / 1000) - 30 }
            ], (ev) => {
                const pkt = decryptPacket(ev.content, this.key, this.cID);
                if (pkt && pkt.type === 'viewer_alive' && pkt.vid) {
                    this.relayViewers.set(pkt.vid, Date.now());
                    this._pruneRelayViewers();
                    this._emitStatus();
                }
            });

            // 2. Start PeerJS WebRTC Host in parallel
            this._initSharerPeer();

            // Watchdog to prune stale relay viewers & auto-heal WebRTC signaling
            this.peerWatchdogTimer = setInterval(() => {
                if (this.destroyed || this.mode !== 'sharer') return;
                this._pruneRelayViewers();
                if (this.peer && this.peer.disconnected && !this.peer.destroyed) {
                    try { this.peer.reconnect(); } catch { /* ignore */ }
                }
                this._emitStatus();
            }, 8000);

            this._emitStatus();
        }

        _initSharerPeer() {
            if (this.destroyed || typeof Peer === 'undefined') return;
            if (this.peer) {
                try { this.peer.destroy(); } catch { /* ignore */ }
                this.peer = null;
            }
            try {
                this.peer = new Peer(this.cID, PEER_CONFIG);
            } catch {
                this._emitStatus();
                return;
            }

            this.peer.on('open', () => {
                this._emitStatus();
            });

            this.peer.on('connection', (conn) => {
                conn.on('open', () => {
                    this.viewerConns.add(conn);
                    this._emitStatus();
                    if (this.lastBroadcastPayload) {
                        this._sendWebRtcToConn(conn, this.lastBroadcastPayload);
                    }
                });
                conn.on('close', () => {
                    this.viewerConns.delete(conn);
                    this._emitStatus();
                });
                conn.on('error', () => {
                    this.viewerConns.delete(conn);
                    this._emitStatus();
                });
            });

            this.peer.on('disconnected', () => {
                this._emitStatus();
                if (!this.destroyed && this.peer && !this.peer.destroyed) {
                    setTimeout(() => {
                        try {
                            if (this.peer && this.peer.disconnected && !this.peer.destroyed) {
                                this.peer.reconnect();
                            }
                        } catch { /* ignore */ }
                    }, 1500);
                }
            });

            this.peer.on('error', (err) => {
                // Relay Mesh keeps everything live even if PeerJS server hits temporary issues
                if (err && err.type === 'unavailable-id' && !this.destroyed && this.mode === 'sharer') {
                    setTimeout(() => {
                        if (!this.destroyed && this.mode === 'sharer' && (!this.peer || this.peer.destroyed || !this.peer.open)) {
                            this._initSharerPeer();
                        }
                    }, 3500);
                }
                this._emitStatus();
            });
        }

        broadcastSharerPacket(packet, options) {
            if (this.destroyed || this.mode !== 'sharer' || !this.key) return { webrtcSent: 0, relaySent: 0 };
            const opts = options || {};
            const enriched = Object.assign({}, packet, {
                v: 2,
                cID: this.cID,
                seq: this._nextSeq(),
                ts: Date.now()
            });

            if (enriched.type === 'init' || enriched.type === 'update') {
                this.lastBroadcastPayload = enriched;
            }

            const encrypted = encryptPacket(enriched, this.key);

            // 1. Send over all active WebRTC DataChannels (sub-100ms P2P)
            let webrtcSent = 0;
            this.viewerConns.forEach((conn) => {
                if (conn && conn.open) {
                    try {
                        conn.send(encrypted);
                        webrtcSent++;
                    } catch { /* ignore */ }
                }
            });

            // 2. Publish over Multi-Relay Nostr Mesh
            let relaySent = 0;
            const now = Date.now();
            const isCritical = enriched.type === 'init' || enriched.type === 'stopped' || Boolean(opts.forceSnapshot);
            const allowEphPing = enriched.type === 'ping' && Boolean(opts.relayPing);

            if (this.relayMesh && (enriched.type !== 'ping' || allowEphPing)) {
                // Ephemeral stream event (max ~1.25/sec) for live movement or keepalive pings
                if (isCritical || now - this.lastEphAtMs >= 800) {
                    const ephEvent = signNostrEvent(20000, [], encrypted, this.sharerId);
                    relaySent += this.relayMesh.publish(ephEvent);
                    this.lastEphAtMs = now;
                }

                // Replaceable snapshot event (every >=3s or immediately on critical state, NEVER overwritten by 'ping')
                if (enriched.type !== 'ping') {
                    const nowSec = Math.floor(now / 1000);
                    if (isCritical || now - this.lastSnapshotAtMs >= 3200) {
                        const snapSec = Math.max(nowSec, this.lastSnapshotSec + 1);
                        // Cap future drift at +10s to stay accepted by all strict relays
                        const safeSec = Math.min(snapSec, nowSec + 10);
                        this.lastSnapshotSec = safeSec;
                        this.lastSnapshotAtMs = now;
                        const snapEvent = signNostrEvent(
                            30078,
                            [['d', this.sharerId.dTag]],
                            encrypted,
                            this.sharerId,
                            safeSec
                        );
                        relaySent += this.relayMesh.publish(snapEvent);
                    }
                }
            }

            return { webrtcSent, relaySent, totalTransports: (webrtcSent > 0 ? 1 : 0) + (relaySent > 0 ? 1 : 0) };
        }

        _sendWebRtcToConn(conn, packet) {
            try {
                if (conn && conn.open) {
                    conn.send(encryptPacket(packet, this.key));
                }
            } catch { /* ignore */ }
        }

        startViewer(cID, secretKey) {
            this.stop();
            this.destroyed = false;
            this.mode = 'viewer';
            this.cID = cID;
            this.key = secretKey;
            this.highestReceivedSeq = 0;
            this.sharerId = deriveChannelIdentity(this.cID, this.key, 'sharer');
            this.viewerId = deriveChannelIdentity(this.cID, this.key, 'viewer');

            // 1. Nostr Mesh: pull latest replaceable snapshot (kind 30078) + stream ephemeral live fixes (kind 20000)
            this.relayMesh = new NostrRelayMesh(NOSTR_RELAYS, {
                onHealthChange: () => {
                    this._sendViewerPresence();
                    this._emitStatus();
                }
            });
            this.relayMesh.connect();
            this.relayMesh.subscribe('sharer-stream', [
                { authors: [this.sharerId.pubHex], kinds: [30078], limit: 1 },
                { authors: [this.sharerId.pubHex], kinds: [20000], since: Math.floor(Date.now() / 1000) - 10 }
            ], (ev) => {
                const pkt = decryptPacket(ev.content, this.key, this.cID);
                if (pkt) {
                    this._handleViewerPacket(pkt, 'relay');
                }
            });

            this.viewerPresenceTimer = setInterval(() => {
                if (!this.destroyed && this.mode === 'viewer') {
                    this._sendViewerPresence();
                }
            }, 10000);

            // 2. PeerJS WebRTC Viewer in parallel for sub-100ms P2P when direct route works
            this._initViewerPeer();
            this._emitStatus();
        }

        _sendViewerPresence() {
            if (!this.relayMesh || this.relayMesh.getOpenCount() === 0 || this.destroyed) return;
            const pkt = {
                v: 2,
                cID: this.cID,
                type: 'viewer_alive',
                vid: this.localViewerId,
                ts: Date.now()
            };
            const encrypted = encryptPacket(pkt, this.key);
            const ev = signNostrEvent(20001, [], encrypted, this.viewerId);
            this.relayMesh.publish(ev);
        }

        _initViewerPeer() {
            if (this.destroyed || typeof Peer === 'undefined') return;
            if (this.peer) {
                try { this.peer.destroy(); } catch { /* ignore */ }
                this.peer = null;
            }
            try {
                this.peer = new Peer(PEER_CONFIG);
            } catch {
                this._scheduleViewerPeerReconnect(4000);
                return;
            }

            this.peer.on('open', () => {
                this._connectViewerWebRtc();
            });
            this.peer.on('error', () => {
                this._scheduleViewerPeerReconnect(4500);
                this._emitStatus();
            });
            this.peer.on('disconnected', () => {
                if (!this.destroyed && this.peer && !this.peer.destroyed) {
                    try { this.peer.reconnect(); } catch { /* ignore */ }
                }
            });
        }

        _connectViewerWebRtc() {
            if (this.destroyed || !this.peer || this.peer.destroyed || !this.cID) return;
            if (this.viewerConn) {
                try { this.viewerConn.close(); } catch { /* ignore */ }
                this.viewerConn = null;
            }

            const conn = this.peer.connect(this.cID, { reliable: true });
            this.viewerConn = conn;

            conn.on('open', () => {
                if (this.viewerReconnectTimer) {
                    clearTimeout(this.viewerReconnectTimer);
                    this.viewerReconnectTimer = null;
                }
                this._emitStatus();
            });

            conn.on('data', (encrypted) => {
                const pkt = decryptPacket(encrypted, this.key, this.cID);
                if (pkt) {
                    this._handleViewerPacket(pkt, 'webrtc');
                } else if (this.callbacks.onDecryptError) {
                    this.callbacks.onDecryptError();
                }
            });

            conn.on('close', () => {
                this.viewerConn = null;
                this._emitStatus();
                this._scheduleViewerPeerReconnect(4000);
            });

            conn.on('error', () => {
                this.viewerConn = null;
                this._emitStatus();
                this._scheduleViewerPeerReconnect(4500);
            });
        }

        _scheduleViewerPeerReconnect(delayMs) {
            if (this.destroyed || this.mode !== 'viewer' || this.viewerReconnectTimer) return;
            this.viewerReconnectTimer = setTimeout(() => {
                this.viewerReconnectTimer = null;
                if (this.destroyed || this.mode !== 'viewer') return;
                if (this.peer && !this.peer.destroyed) {
                    this._connectViewerWebRtc();
                } else {
                    this._initViewerPeer();
                }
            }, delayMs);
        }

        _handleViewerPacket(pkt, viaTransport) {
            if (this.destroyed) return;

            // Keepalive ping handles connection freshness regardless of seq
            if (pkt.type === 'ping') {
                if (this.callbacks.onPacket) {
                    this.callbacks.onPacket(pkt, viaTransport);
                }
                return;
            }

            const incomingSeq = Number.isFinite(pkt.seq) ? pkt.seq : (Number.isFinite(pkt.ts) ? pkt.ts : 0);
            if (incomingSeq > 0 && incomingSeq <= this.highestReceivedSeq && pkt.type !== 'stopped') {
                // Already received an equal or newer packet over the parallel transport
                return;
            }
            if (incomingSeq > this.highestReceivedSeq) {
                this.highestReceivedSeq = incomingSeq;
            }

            if (this.callbacks.onPacket) {
                this.callbacks.onPacket(pkt, viaTransport);
            }
        }

        _pruneRelayViewers() {
            const cutoff = Date.now() - 28000;
            this.relayViewers.forEach((ts, vid) => {
                if (ts < cutoff) this.relayViewers.delete(vid);
            });
        }

        getStatusSnapshot() {
            const relaysOpen = this.relayMesh ? this.relayMesh.getOpenCount() : 0;
            const totalRelays = NOSTR_RELAYS.length;
            const webrtcOpen = this.mode === 'sharer'
                ? Array.from(this.viewerConns).filter(c => c && c.open).length
                : (this.viewerConn && this.viewerConn.open ? 1 : 0);
            const peerReady = Boolean(this.peer && this.peer.open && !this.peer.destroyed);
            this._pruneRelayViewers();

            const approxViewerCount = Math.max(webrtcOpen, this.relayViewers.size);
            return {
                mode: this.mode,
                relaysOpen,
                totalRelays,
                peerReady,
                webrtcOpen,
                relayViewers: this.relayViewers.size,
                approxViewerCount
            };
        }

        _emitStatus() {
            if (this.callbacks.onStatusChange) {
                this.callbacks.onStatusChange(this.getStatusSnapshot());
            }
        }

        resume() {
            if (this.destroyed) return;
            if (this.relayMesh) {
                this.relayMesh.ensureConnected();
            }
            if (this.peer && this.peer.disconnected && !this.peer.destroyed) {
                try { this.peer.reconnect(); } catch { /* ignore */ }
            }
            if (this.mode === 'viewer') {
                this._sendViewerPresence();
                if (!this.viewerConn || !this.viewerConn.open) {
                    this._connectViewerWebRtc();
                }
            }
            this._emitStatus();
        }

        stop() {
            this.destroyed = true;
            if (this.viewerPresenceTimer) {
                clearInterval(this.viewerPresenceTimer);
                this.viewerPresenceTimer = null;
            }
            if (this.viewerReconnectTimer) {
                clearTimeout(this.viewerReconnectTimer);
                this.viewerReconnectTimer = null;
            }
            if (this.peerWatchdogTimer) {
                clearInterval(this.peerWatchdogTimer);
                this.peerWatchdogTimer = null;
            }
            if (this.viewerConn) {
                try { this.viewerConn.close(); } catch { /* ignore */ }
                this.viewerConn = null;
            }
            this.viewerConns.forEach((c) => {
                try { c.close(); } catch { /* ignore */ }
            });
            this.viewerConns.clear();
            this.relayViewers.clear();
            if (this.peer) {
                try { this.peer.destroy(); } catch { /* ignore */ }
                this.peer = null;
            }
            if (this.relayMesh) {
                this.relayMesh.destroy();
                this.relayMesh = null;
            }
            this.mode = null;
        }
    }

    const exported = {
        ICE_SERVERS,
        PEER_CONFIG,
        NOSTR_RELAYS,
        deriveChannelIdentity,
        signNostrEvent,
        encryptPacket,
        decryptPacket,
        NostrRelayMesh,
        HybridSessionManager
    };

    if (typeof module !== 'undefined' && module.exports) {
        module.exports = exported;
    } else {
        global.PNearSync = exported;
    }
})(typeof window !== 'undefined' ? window : globalThis);
