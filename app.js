/**
 * P-Near: Zero-Backend Live Location Sharing Orchestrator
 * Coordinates Synchronous-First Adaptive Geolocation (geo.js),
 * Hybrid WebRTC + E2EE Multi-Relay Mesh (sync.js), Leaflet Map Renderer, and Accessible UI.
 */
(function () {
    'use strict';

    const Geo = window.PNearGeo;
    const Sync = window.PNearSync;

    // High-Detail Map Tile Configurations (Streets up to Zoom 19 + Esri Satellite Mode)
    const MAP_THEMES = {
        streets: {
            url: 'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
            attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors'
        },
        streetsFallback: {
            url: 'https://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}',
            attribution: '&copy; <a href="https://www.esri.com/">Esri</a>, DeLorme, NAVTEQ, USGS, Intermap, iPC, NRCAN, Esri Japan'
        },
        satellite: {
            url: 'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',
            attribution: '&copy; <a href="https://www.esri.com/">Esri</a>, Maxar, Earthstar Geographics'
        }
    };

    const state = {
        theme: 'dark',
        mapStyle: 'streets', // 'streets' | 'satellite'
        mode: 'dashboard', // 'dashboard' | 'sharing' | 'viewer'
        autoFollow: true,
        isDemoRunning: false,
        demoInterval: null,

        // Subsystems
        geoTracker: null,
        sync: null,
        wakeLock: null,

        // Sharer Active Session
        activeShare: null, // { cID, key, name, exp, duration }
        packetCount: 0,
        lastCoords: null,
        coordsHistory: [],
        totalDistanceMeters: 0,
        lastUpdateSentAt: 0,
        heartbeatInterval: null,

        // Viewer Tracking Session
        viewer: {
            cID: null,
            key: null,
            sharerName: 'Someone',
            exp: null,
            coords: null,
            tripDistanceMeters: 0,
            history: [],
            lastPingTime: null,
            lastTransport: null,
            isEnded: false,
            myWatchId: null,
            myCoords: null
        },

        // Leaflet Map Objects & Animation
        map: null,
        tileLayer: null,
        usingOsmFallback: false,
        tileErrorCount: 0,
        sharerMarker: null,
        sharerAccuracyCircle: null,
        viewerMarker: null,
        breadcrumbsPolyline: null,
        markerAnimations: {}
    };

    const el = {
        themeToggle: document.getElementById('theme-toggle'),
        btnMapStyle: document.getElementById('btn-map-style'),
        mapParotBadge: document.getElementById('map-parot-badge'),
        dashboardView: document.getElementById('dashboard-view'),
        sharingView: document.getElementById('sharing-view'),
        viewerView: document.getElementById('viewer-view'),
        mapContainer: document.getElementById('map-container'),

        // Dashboard
        sharerNameInput: document.getElementById('sharer-name'),
        durationButtons: document.querySelectorAll('.duration-btn'),
        btnStartShare: document.getElementById('btn-start-share'),

        // Sharer
        sharingCard: document.getElementById('sharing-card'),
        sharerPulse: document.getElementById('sharer-pulse'),
        sharingTimer: document.getElementById('sharing-timer'),
        btnToggleSharePanel: document.getElementById('btn-toggle-share-panel'),
        gpsRecoveryBox: document.getElementById('gps-recovery-box'),
        gpsRecoveryTitle: document.getElementById('gps-recovery-title'),
        gpsRecoveryHint: document.getElementById('gps-recovery-hint'),
        btnRetryGps: document.getElementById('btn-retry-gps'),
        btnDemoLocation: document.getElementById('btn-demo-location'),
        shareUrlInput: document.getElementById('share-url'),
        btnCopyLink: document.getElementById('btn-copy-link'),
        copyStatusTip: document.getElementById('copy-status-tip'),
        btnShareApi: document.getElementById('btn-share-api'),
        statAccuracy: document.getElementById('stat-accuracy'),
        statSpeed: document.getElementById('stat-speed'),
        statDistance: document.getElementById('stat-distance'),
        statPackets: document.getElementById('stat-packets'),
        wifiIconWrap: document.getElementById('wifi-icon-wrap'),
        networkStatusText: document.getElementById('network-status-text'),
        btnCenterSharer: document.getElementById('btn-center-sharer'),
        btnStopShare: document.getElementById('btn-stop-share'),

        // Viewer
        viewerCard: document.getElementById('viewer-card'),
        viewerSharerName: document.getElementById('viewer-sharer-name'),
        viewerTimer: document.getElementById('viewer-timer'),
        viewerStatusText: document.getElementById('viewer-status-text'),
        viewerPulse: document.getElementById('viewer-pulse'),
        viewerAccuracyPill: document.getElementById('viewer-accuracy-pill'),
        btnToggleViewerPanel: document.getElementById('btn-toggle-viewer-panel'),
        viewStatSpeed: document.getElementById('view-stat-speed'),
        viewStatDistance: document.getElementById('view-stat-distance'),
        viewStatTrip: document.getElementById('view-stat-trip'),
        viewStatPing: document.getElementById('view-stat-ping'),
        btnDirections: document.getElementById('btn-directions'),
        btnRecenter: document.getElementById('btn-recenter'),
        recenterLabel: document.getElementById('recenter-label'),
        btnToggleMyLocation: document.getElementById('btn-toggle-my-location'),

        // Modal & Overlays
        stopShareDialog: document.getElementById('stop-share-dialog'),
        toastContainer: document.getElementById('toast-container'),
        globalLoader: document.getElementById('global-loader'),
        loaderText: document.getElementById('loader-text')
    };

    // --- INITIALIZATION ---

    document.addEventListener('DOMContentLoaded', () => {
        if (window.lucide) {
            lucide.createIcons();
        }

        initThemeSystem();
        setupEventListeners();
        setupStopDialog();
        routeApp();

        if ('serviceWorker' in navigator && location.protocol === 'https:') {
            navigator.serviceWorker.register('sw.js').catch(() => {});
        }

        setInterval(updateCountdownTimers, 1000);
    });

    // --- THEME SYSTEM ---

    function getSystemPreferredTheme() {
        return window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
    }

    function initThemeSystem() {
        let saved = null;
        try {
            saved = localStorage.getItem('pnear-theme');
        } catch { /* ignore storage restrictions */ }
        applyResolvedTheme(saved === 'light' || saved === 'dark' ? saved : getSystemPreferredTheme(), saved);

        if (window.matchMedia) {
            const mq = window.matchMedia('(prefers-color-scheme: dark)');
            const onOsThemeChange = () => {
                let stored = null;
                try { stored = localStorage.getItem('pnear-theme'); } catch { /* ignore */ }
                if (!stored) {
                    applyResolvedTheme(getSystemPreferredTheme(), null);
                }
            };
            if (mq.addEventListener) mq.addEventListener('change', onOsThemeChange);
        }

        window.addEventListener('storage', (e) => {
            if (e.key === 'pnear-theme') {
                const next = e.newValue === 'light' || e.newValue === 'dark' ? e.newValue : getSystemPreferredTheme();
                applyResolvedTheme(next, e.newValue);
            }
        });
    }

    function applyResolvedTheme(resolvedTheme, storedOverride) {
        state.theme = resolvedTheme;
        document.documentElement.setAttribute('data-theme', resolvedTheme);
        const meta = document.querySelector('meta[name="color-scheme"]');
        if (meta) {
            meta.content = (storedOverride === 'light' || storedOverride === 'dark') ? storedOverride : 'light dark';
        }

        if (state.map) {
            attachTileLayer(resolvedTheme);
        }
    }

    function toggleTheme() {
        const nextTheme = state.theme === 'dark' ? 'light' : 'dark';
        const sysTheme = getSystemPreferredTheme();
        try {
            if (nextTheme === sysTheme) {
                localStorage.removeItem('pnear-theme');
                applyResolvedTheme(nextTheme, null);
            } else {
                localStorage.setItem('pnear-theme', nextTheme);
                applyResolvedTheme(nextTheme, nextTheme);
            }
        } catch {
            applyResolvedTheme(nextTheme, nextTheme);
        }
    }

    // --- ROUTER & SESSION RESTORATION ---

    function routeApp() {
        const urlParams = new URLSearchParams(window.location.search);
        const shareCID = urlParams.get('share');
        const hashKey = window.location.hash ? window.location.hash.substring(1) : null;

        if (shareCID && hashKey) {
            startViewerMode(shareCID, hashKey);
            return;
        }

        let storedShare = null;
        try {
            storedShare = localStorage.getItem('pnear-active-share');
        } catch { /* ignore */ }

        if (storedShare) {
            try {
                const parsed = JSON.parse(storedShare);
                if (parsed && parsed.cID && parsed.key && parsed.exp > Date.now()) {
                    restoreSharerSession(parsed);
                    return;
                }
                localStorage.removeItem('pnear-active-share');
            } catch {
                try { localStorage.removeItem('pnear-active-share'); } catch { /* ignore */ }
            }
        }

        state.mode = 'dashboard';
        switchView('dashboard');
    }

    function restoreSharerSession(parsed) {
        state.activeShare = parsed;
        state.mode = 'sharing';
        state.autoFollow = true;
        state.coordsHistory = Array.isArray(parsed.history) ? parsed.history : [];
        state.totalDistanceMeters = Number(parsed.dist) || 0;

        el.shareUrlInput.value = buildShareUrl(parsed.cID, parsed.key);
        el.statDistance.innerText = Geo.formatDistance(state.totalDistanceMeters);
        el.statAccuracy.innerText = 'Checking GPS...';
        el.statSpeed.innerText = '--';
        el.statPackets.innerText = '0';

        switchView('sharing');
        initMap();
        startSyncEngineForSharer();

        // When restoring after reload (without click gesture), inspect permission first
        // so Safari "Ask" doesn't silently fail before the user sees the resume button.
        Geo.queryGeoPermissionState().then((perm) => {
            if (state.mode !== 'sharing') return;
            const env = Geo.detectBrowserGeoEnvironment();
            if (perm === 'granted') {
                startGeoTrackingSync();
            } else if (perm === 'denied') {
                showGpsRecovery(
                    'Location Access Blocked',
                    env.steps
                );
                el.statAccuracy.innerText = 'GPS Blocked';
            } else if (env.isSafari) {
                showGpsRecovery(
                    'Session Restored — Tap to Resume GPS',
                    'Safari requires a button tap after page reload to resume live location updates.'
                );
                el.statAccuracy.innerText = 'Tap Enable GPS';
            } else {
                startGeoTrackingSync();
            }
        });
    }

    function buildShareUrl(cID, key) {
        return `${window.location.origin}${window.location.pathname}?share=${encodeURIComponent(cID)}#${key}`;
    }

    function switchView(viewName) {
        [el.dashboardView, el.sharingView, el.viewerView].forEach((panel) => {
            panel.classList.add('hidden');
            panel.classList.remove('active');
        });

        if (viewName === 'dashboard') {
            el.dashboardView.classList.remove('hidden');
            el.dashboardView.classList.add('active');
            el.mapContainer.classList.add('hidden');
            if (el.btnMapStyle) el.btnMapStyle.classList.add('hidden');
            if (el.mapParotBadge) el.mapParotBadge.classList.add('hidden');
        } else if (viewName === 'sharing') {
            el.sharingView.classList.remove('hidden');
            el.sharingView.classList.add('active');
            el.mapContainer.classList.remove('hidden');
            if (el.btnMapStyle) el.btnMapStyle.classList.remove('hidden');
            if (el.mapParotBadge) el.mapParotBadge.classList.remove('hidden');
        } else if (viewName === 'viewer') {
            el.viewerView.classList.remove('hidden');
            el.viewerView.classList.add('active');
            el.mapContainer.classList.remove('hidden');
            if (el.btnMapStyle) el.btnMapStyle.classList.remove('hidden');
            if (el.mapParotBadge) el.mapParotBadge.classList.remove('hidden');
        }
    }

    // --- EVENT LISTENERS ---

    function setupEventListeners() {
        el.themeToggle.addEventListener('click', toggleTheme);
        if (el.btnMapStyle) {
            el.btnMapStyle.addEventListener('click', toggleMapStyle);
        }

        el.durationButtons.forEach((btn) => {
            btn.addEventListener('click', () => {
                el.durationButtons.forEach(b => b.classList.remove('active'));
                btn.classList.add('active');
            });
        });

        el.btnStartShare.addEventListener('click', handleStartShare);
        el.btnRetryGps.addEventListener('click', handleRetryGpsClick);
        el.btnDemoLocation.addEventListener('click', handleStartDemoMovement);
        el.btnCopyLink.addEventListener('click', copyShareLink);
        el.btnShareApi.addEventListener('click', shareViaApi);
        el.btnStopShare.addEventListener('click', openStopConfirmDialog);
        el.btnCenterSharer.addEventListener('click', recenterMapOnSharer);

        el.btnToggleSharePanel.addEventListener('click', () => {
            el.sharingCard.classList.toggle('collapsed');
        });
        el.btnToggleViewerPanel.addEventListener('click', () => {
            el.viewerCard.classList.toggle('collapsed');
        });

        el.btnRecenter.addEventListener('click', recenterMapOnSharer);
        el.btnDirections.addEventListener('click', openDirections);
        el.btnToggleMyLocation.addEventListener('click', toggleViewerLocation);

        document.addEventListener('visibilitychange', handleVisibilityChange);
    }

    function setupStopDialog() {
        const dialog = el.stopShareDialog;
        if (!dialog) return;

        let resolvedThisOpen = false;
        const form = dialog.querySelector('form');

        const finalize = (val) => {
            if (resolvedThisOpen) return;
            resolvedThisOpen = true;
            if (val === 'stop') {
                stopLocationSharing(false);
            }
        };

        if (form) {
            form.addEventListener('submit', (e) => {
                e.preventDefault();
                const submitter = e.submitter;
                const val = submitter && submitter.value ? submitter.value : 'cancel';
                dialog.returnValue = '';
                if (dialog.open) dialog.close(val);
                finalize(val);
            });
        }

        dialog.addEventListener('close', () => {
            const val = dialog.returnValue;
            dialog.returnValue = '';
            finalize(val);
            resolvedThisOpen = false;
        });

        // Light-dismiss fallback when clicking backdrop in browsers lacking closedby support
        let pressedOutside = false;
        const outside = (e) => {
            const r = dialog.getBoundingClientRect();
            return e.clientX < r.left || e.clientX > r.right || e.clientY < r.top || e.clientY > r.bottom;
        };
        dialog.addEventListener('pointerdown', (e) => {
            if (dialog.open) pressedOutside = outside(e);
        });
        dialog.addEventListener('pointerup', (e) => {
            if (dialog.open && pressedOutside && outside(e)) {
                dialog.close('cancel');
            }
            pressedOutside = false;
        });

        dialog._resetStopGuard = () => {
            resolvedThisOpen = false;
        };
    }

    function openStopConfirmDialog() {
        if (el.stopShareDialog && typeof el.stopShareDialog.showModal === 'function') {
            if (el.stopShareDialog._resetStopGuard) el.stopShareDialog._resetStopGuard();
            el.stopShareDialog.showModal();
        } else {
            stopLocationSharing(false);
        }
    }

    // --- SHARER WORKFLOW ---

    function handleStartShare() {
        if (!navigator.geolocation) {
            showToast('Geolocation is not supported by your browser.', 'error');
            return;
        }

        const rawName = el.sharerNameInput.value.trim();
        const sharerName = rawName || 'Anonymous Friend';
        const activeDurationBtn = document.querySelector('.duration-btn.active');
        const minutes = activeDurationBtn ? (parseInt(activeDurationBtn.getAttribute('data-minutes'), 10) || 60) : 60;

        const cID = 'pnear_' + generateRandomId(12);
        const key = generateRandomId(32);
        const exp = Date.now() + (minutes * 60 * 1000);

        state.activeShare = { cID, key, name: sharerName, exp, duration: minutes };
        state.packetCount = 0;
        state.lastCoords = null;
        state.coordsHistory = [];
        state.totalDistanceMeters = 0;
        state.autoFollow = true;
        state.isDemoRunning = false;

        try {
            localStorage.setItem('pnear-active-share', JSON.stringify(state.activeShare));
        } catch { /* ignore storage quota error */ }

        el.shareUrlInput.value = buildShareUrl(cID, key);
        el.statAccuracy.innerText = 'Acquiring...';
        el.statSpeed.innerText = '--';
        el.statDistance.innerText = '0 m';
        el.statPackets.innerText = '0';
        hideGpsRecovery();

        state.mode = 'sharing';
        switchView('sharing');
        initMap();

        // CRITICAL FOR iOS / macOS SAFARI:
        // Invoke geolocation synchronously inside the click gesture stack BEFORE async network setup!
        startGeoTrackingSync();

        startSyncEngineForSharer();
        requestWakeLock();
        showToast('Session started! Requesting live location...', 'info');
    }

    function startGeoTrackingSync() {
        stopDemoMovement();

        if (!state.geoTracker) {
            state.geoTracker = new Geo.AdaptiveGeoTracker({
                onPosition: handleGpsPosition,
                onError: handleGeoTrackerError,
                onStatus: (_status, msg) => {
                    if (!state.lastCoords) {
                        el.statAccuracy.innerText = msg;
                    }
                },
                onModeChange: (mode) => {
                    if (mode === 'high' && !state.lastCoords) {
                        el.statAccuracy.innerText = 'Locking GPS...';
                    }
                }
            });
        }

        state.geoTracker.startSync();
    }

    function handleRetryGpsClick() {
        hideGpsRecovery();
        el.statAccuracy.innerText = 'Retrying GPS...';
        el.sharerPulse.className = 'pulse-dot amber';
        startGeoTrackingSync();
    }

    function handleGpsPosition(position) {
        const result = Geo.processGpsReading(position, { lastCoords: state.lastCoords });
        if (!result.accepted) return;

        hideGpsRecovery();
        el.sharerPulse.className = 'pulse-dot red';

        const isFirstCoordFix = !state.lastCoords;
        const coordObj = result.coordObj;
        state.lastCoords = coordObj;
        state.totalDistanceMeters += result.addedDistanceMeters;

        const histLen = state.coordsHistory.length;
        if (histLen === 0 || state.coordsHistory[histLen - 1][0] !== coordObj.lat || state.coordsHistory[histLen - 1][1] !== coordObj.lng) {
            state.coordsHistory.push([coordObj.lat, coordObj.lng]);
            if (state.coordsHistory.length > 250) {
                state.coordsHistory.shift();
            }
        }

        el.statAccuracy.innerText = `±${coordObj.acc} m`;
        el.statSpeed.innerText = `${coordObj.spd} km/h`;
        el.statDistance.innerText = Geo.formatDistance(state.totalDistanceMeters);

        // Persist lightweight restore snapshot
        try {
            if (state.activeShare) {
                localStorage.setItem('pnear-active-share', JSON.stringify({
                    ...state.activeShare,
                    dist: Math.round(state.totalDistanceMeters),
                    history: state.coordsHistory.slice(-60)
                }));
            }
        } catch { /* ignore */ }

        updateSharerMap(coordObj);
        broadcastFullLocationUpdate(coordObj, isFirstCoordFix);
    }

    function handleGeoTrackerError(kind, _rawErr, envInfo) {
        if (kind === 'denied') {
            el.statAccuracy.innerText = 'GPS Denied';
            el.sharerPulse.className = 'pulse-dot amber';
            showGpsRecovery(
                `Location Blocked in ${envInfo.browserName}`,
                envInfo.steps
            );
            showToast('Location permission needed. Check the recovery guide below.', 'warning');
        } else if (kind === 'unavailable') {
            el.statAccuracy.innerText = 'Unavailable';
            el.sharerPulse.className = 'pulse-dot amber';
            showGpsRecovery(
                'GPS / WiFi Position Unavailable',
                'Ensure Location Services is enabled on this device and retry, or preview using Simulate Route.'
            );
        } else {
            el.statAccuracy.innerText = 'Unsupported';
            showGpsRecovery(
                'Geolocation Unsupported',
                'This browser does not support Geolocation. You can test the platform using Simulate Route.'
            );
        }
    }

    function showGpsRecovery(title, hint) {
        if (!el.gpsRecoveryBox) return;
        el.gpsRecoveryTitle.innerText = title;
        el.gpsRecoveryHint.innerText = hint;
        el.gpsRecoveryBox.classList.remove('hidden');
    }

    function hideGpsRecovery() {
        if (el.gpsRecoveryBox) {
            el.gpsRecoveryBox.classList.add('hidden');
        }
    }

    function handleStartDemoMovement() {
        if (state.geoTracker) {
            state.geoTracker.stop();
        }
        hideGpsRecovery();
        state.isDemoRunning = true;
        el.sharerPulse.className = 'pulse-dot red';
        showToast('Demo simulation running across Cairo.', 'info');

        let lat = state.lastCoords ? state.lastCoords.lat : 30.0444;
        let lng = state.lastCoords ? state.lastCoords.lng : 31.2357;
        let step = 0;

        if (state.demoInterval) clearInterval(state.demoInterval);

        const emitStep = () => {
            if (!state.activeShare || state.mode !== 'sharing') return;
            step++;
            const dLat = 0.00025 + Math.sin(step * 0.4) * 0.00008;
            const dLng = 0.00032 + Math.cos(step * 0.4) * 0.00008;
            lat += dLat;
            lng += dLng;

            handleGpsPosition({
                coords: {
                    latitude: lat,
                    longitude: lng,
                    accuracy: 8,
                    speed: (28 + Math.sin(step) * 8) / 3.6,
                    heading: Math.round(Geo.calculateBearingDeg({ lat: lat - dLat, lng: lng - dLng }, { lat, lng }) || 45)
                },
                timestamp: Date.now()
            });
        };

        emitStep();
        state.demoInterval = setInterval(emitStep, 1600);
    }

    function stopDemoMovement() {
        state.isDemoRunning = false;
        if (state.demoInterval) {
            clearInterval(state.demoInterval);
            state.demoInterval = null;
        }
    }

    // --- SYNC ORCHESTRATION (SHARER & VIEWER) ---

    function ensureSyncManager() {
        if (state.sync) return state.sync;
        state.sync = new Sync.HybridSessionManager({
            onStatusChange: handleSyncStatusChange,
            onPacket: handleViewerPacket,
            onDecryptError: () => {
                showToast('Decryption failed: Invalid security key in URL.', 'error');
            }
        });
        return state.sync;
    }

    function startSyncEngineForSharer() {
        if (!state.activeShare) return;
        const sync = ensureSyncManager();
        sync.startSharer(state.activeShare);

        // Immediately publish session metadata snapshot so viewers joining early get name + countdown cleanly
        sync.broadcastSharerPacket({
            type: 'init',
            name: state.activeShare.name,
            exp: state.activeShare.exp,
            coords: state.lastCoords,
            dist: Math.round(state.totalDistanceMeters),
            history: state.coordsHistory.slice(-60)
        }, { forceSnapshot: true });

        startSharerHeartbeat();
    }

    function broadcastFullLocationUpdate(coords, forceSnapshot) {
        if (!state.activeShare || !state.sync) return;

        const packet = {
            type: 'update',
            name: state.activeShare.name,
            exp: state.activeShare.exp,
            coords,
            dist: Math.round(state.totalDistanceMeters),
            history: state.coordsHistory.slice(-60)
        };

        const res = state.sync.broadcastSharerPacket(packet, { forceSnapshot: Boolean(forceSnapshot) });
        state.lastUpdateSentAt = Date.now();
        const snap = state.sync.getStatusSnapshot();
        if (res.webrtcSent > 0 || res.relaySent > 0 || snap.relaysOpen > 0 || snap.peerReady || forceSnapshot) {
            state.packetCount++;
            el.statPackets.innerText = state.packetCount;
        }
    }

    function startSharerHeartbeat() {
        if (state.heartbeatInterval) clearInterval(state.heartbeatInterval);

        state.heartbeatInterval = setInterval(() => {
            if (!state.activeShare || !state.sync || state.mode !== 'sharing') return;
            const snap = state.sync.getStatusSnapshot();
            const silentMs = Date.now() - state.lastUpdateSentAt;
            // Send lightweight keepalive over WebRTC always, or ephemeral relay ping if stationary >= 15s
            if (snap.webrtcOpen > 0 || silentMs >= 15000) {
                state.sync.broadcastSharerPacket(
                    { type: 'ping', time: Date.now() },
                    { relayPing: silentMs >= 15000 }
                );
            }
        }, 6000);
    }

    function handleSyncStatusChange(snap) {
        if (state.mode === 'sharing') {
            const parts = [];
            if (snap.peerReady && snap.relaysOpen > 0) {
                parts.push(`Dual Mesh Ready (${snap.relaysOpen}/${snap.totalRelays} relays)`);
            } else if (snap.relaysOpen > 0) {
                parts.push(`Relay Mesh Active (${snap.relaysOpen}/${snap.totalRelays})`);
            } else if (snap.peerReady) {
                parts.push('P2P Network Ready');
            }

            if (parts.length === 0) {
                updateNetworkStatus('connecting', 'Connecting to P2P & Relay Mesh...');
                return;
            }

            const viewerLabel = snap.approxViewerCount > 0
                ? `${snap.approxViewerCount} viewer(s) live`
                : 'Ready for viewers';
            updateNetworkStatus('connected', `${parts[0]} • ${viewerLabel}`);
        } else if (state.mode === 'viewer' && !state.viewer.isEnded) {
            updateViewerTransportBanner(snap);
        }
    }

    function stopLocationSharing(isAutoExpired) {
        showLoader('Stopping sharing session...');

        if (state.sync && state.activeShare) {
            state.sync.broadcastSharerPacket({
                type: 'stopped',
                name: state.activeShare.name,
                exp: Date.now()
            }, { forceSnapshot: true });
        }

        stopDemoMovement();

        if (state.heartbeatInterval) {
            clearInterval(state.heartbeatInterval);
            state.heartbeatInterval = null;
        }

        if (state.geoTracker) {
            state.geoTracker.stop();
        }

        releaseWakeLock();

        setTimeout(() => {
            if (state.sync) {
                state.sync.stop();
            }

            try { localStorage.removeItem('pnear-active-share'); } catch { /* ignore */ }
            state.activeShare = null;
            state.coordsHistory = [];
            state.lastCoords = null;
            state.totalDistanceMeters = 0;

            resetMapLayers();
            hideGpsRecovery();
            hideLoader();

            state.mode = 'dashboard';
            switchView('dashboard');

            if (isAutoExpired) {
                showToast('Your sharing session has expired.', 'warning');
            } else {
                showToast('Location sharing stopped.', 'success');
            }
        }, 450);
    }

    // --- VIEWER WORKFLOW ---

    function startViewerMode(cID, key) {
        state.mode = 'viewer';
        state.autoFollow = true;
        state.viewer.cID = cID;
        state.viewer.key = key;
        state.viewer.isEnded = false;
        state.viewer.coords = null;
        state.viewer.history = [];
        state.viewer.lastPingTime = null;
        state.viewer.lastTransport = null;

        el.viewerSharerName.innerText = 'Connecting...';
        el.viewerStatusText.innerText = 'Connecting hybrid P2P + Mesh...';
        el.viewerPulse.className = 'pulse-dot amber';
        el.viewerAccuracyPill.innerText = 'Waiting for GPS...';
        el.viewStatSpeed.innerText = '--';
        el.viewStatTrip.innerText = '0 m';
        el.viewStatPing.innerText = '--';
        updateFollowButtonUI();

        switchView('viewer');
        initMap();

        const sync = ensureSyncManager();
        sync.startViewer(cID, key);
    }

    function updateViewerTransportBanner(snap) {
        if (state.viewer.isEnded) return;
        const hasLiveFix = Boolean(state.viewer.coords);

        if (snap.webrtcOpen > 0 && snap.relaysOpen > 0) {
            el.viewerStatusText.innerText = hasLiveFix ? 'Live • P2P + Mesh' : 'Connected • Waiting for GPS';
            el.viewerPulse.className = hasLiveFix ? 'pulse-dot green' : 'pulse-dot amber';
        } else if (snap.webrtcOpen > 0) {
            el.viewerStatusText.innerText = hasLiveFix ? 'Live • Direct P2P' : 'P2P Connected • Waiting GPS';
            el.viewerPulse.className = hasLiveFix ? 'pulse-dot green' : 'pulse-dot amber';
        } else if (snap.relaysOpen > 0) {
            el.viewerStatusText.innerText = hasLiveFix
                ? `Live • Relay Mesh (${snap.relaysOpen})`
                : `Mesh Online (${snap.relaysOpen}) • Waiting for host`;
            el.viewerPulse.className = hasLiveFix ? 'pulse-dot green' : 'pulse-dot amber';
        } else {
            el.viewerStatusText.innerText = 'Reconnecting to sync mesh...';
            el.viewerPulse.className = 'pulse-dot red';
        }
    }

    function handleViewerPacket(packet, viaTransport) {
        if (state.mode !== 'viewer') return;
        state.viewer.lastTransport = viaTransport;
        state.viewer.lastPingTime = Date.now();

        if (packet.name) {
            state.viewer.sharerName = packet.name;
            el.viewerSharerName.innerText = packet.name;
        }
        if (packet.exp) {
            state.viewer.exp = packet.exp;
        }
        if (Number.isFinite(packet.dist)) {
            state.viewer.tripDistanceMeters = packet.dist;
            el.viewStatTrip.innerText = Geo.formatDistance(packet.dist);
        }

        if (packet.type === 'stopped') {
            state.viewer.isEnded = true;
            el.viewerStatusText.innerText = 'Session stopped by sharer';
            el.viewerPulse.className = 'pulse-dot red';
            el.viewerTimer.innerText = 'Ended';
            showToast(`${state.viewer.sharerName} stopped sharing their location.`, 'warning');
            if (state.sync) state.sync.stop();
            return;
        }

        if (packet.type === 'ping') {
            el.viewStatPing.innerText = 'Just now';
            if (state.sync) updateViewerTransportBanner(state.sync.getStatusSnapshot());
            return;
        }

        if (Array.isArray(packet.history) && packet.history.length > 0) {
            // Merge breadcrumb trail if longer or viewer started fresh mid-session
            if (packet.history.length >= state.viewer.history.length) {
                state.viewer.history = packet.history.slice();
            }
        }

        if (packet.coords) {
            processIncomingViewerCoords(packet.coords);
        } else if (packet.type === 'init') {
            el.viewerStatusText.innerText = 'Waiting for sharer GPS...';
            el.viewerPulse.className = 'pulse-dot amber';
        }
    }

    function processIncomingViewerCoords(coords) {
        state.viewer.coords = { lat: coords.lat, lng: coords.lng, acc: coords.acc, dir: coords.dir };
        state.viewer.lastPingTime = Date.now();

        const qual = Geo.getAccuracyQuality(coords.acc);
        el.viewerAccuracyPill.innerText = `GPS ±${coords.acc} m (${qual.label})`;
        el.viewStatSpeed.innerText = coords.spd !== null && coords.spd !== undefined ? `${coords.spd} km/h` : '0 km/h';
        el.viewStatPing.innerText = 'Just now';

        const hist = state.viewer.history;
        if (hist.length === 0 || hist[hist.length - 1][0] !== coords.lat || hist[hist.length - 1][1] !== coords.lng) {
            hist.push([coords.lat, coords.lng]);
            if (hist.length > 250) hist.shift();
        }

        if (state.sync) {
            updateViewerTransportBanner(state.sync.getStatusSnapshot());
        }

        updateDistanceUI();
        updateViewerMap(coords);
    }

    // --- WAKE LOCK ---

    async function requestWakeLock() {
        if ('wakeLock' in navigator) {
            try {
                state.wakeLock = await navigator.wakeLock.request('screen');
            } catch { /* unsupported or battery saver */ }
        }
    }

    function releaseWakeLock() {
        if (state.wakeLock) {
            state.wakeLock.release().catch(() => {});
            state.wakeLock = null;
        }
    }

    function handleVisibilityChange() {
        if (document.visibilityState !== 'visible') return;
        if (state.mode === 'sharing') {
            requestWakeLock();
        }
        if ((state.mode === 'sharing' || state.mode === 'viewer') && state.sync) {
            state.sync.resume();
        }
    }

    // --- LEAFLET MAP RENDERER ---

    function initMap() {
        if (state.map) {
            state.map.invalidateSize();
            return;
        }

        state.usingOsmFallback = false;
        state.tileErrorCount = 0;

        state.map = L.map('map', {
            zoomControl: true,
            attributionControl: true
        }).setView([26.8206, 30.8025], 5);

        attachTileLayer();
        state.map.zoomControl.setPosition('topright');

        state.map.on('dragstart', () => {
            if (state.autoFollow) {
                state.autoFollow = false;
                updateFollowButtonUI();
            }
        });
    }

    function toggleMapStyle() {
        state.mapStyle = state.mapStyle === 'streets' ? 'satellite' : 'streets';
        state.usingOsmFallback = false;
        if (el.btnMapStyle) {
            el.btnMapStyle.classList.toggle('active', state.mapStyle === 'satellite');
        }
        attachTileLayer();
        showToast(state.mapStyle === 'satellite' ? 'Satellite view enabled' : 'Detailed street view enabled', 'info');
    }

    function attachTileLayer() {
        if (!state.map) return;
        if (state.tileLayer) {
            state.map.removeLayer(state.tileLayer);
        }

        if (state.mapStyle === 'streets') {
            el.mapContainer.classList.add('map-streets-mode');
        } else {
            el.mapContainer.classList.remove('map-streets-mode');
        }

        const cfg = state.mapStyle === 'satellite'
            ? MAP_THEMES.satellite
            : (state.usingOsmFallback ? MAP_THEMES.streetsFallback : MAP_THEMES.streets);
        let tileErrStreak = 0;

        state.tileLayer = L.tileLayer(cfg.url, {
            attribution: cfg.attribution,
            maxZoom: 19
        });

        state.tileLayer.on('tileload', () => {
            tileErrStreak = 0;
        });

        state.tileLayer.on('tileerror', () => {
            tileErrStreak++;
            if (state.mapStyle === 'streets' && !state.usingOsmFallback && tileErrStreak >= 4) {
                state.usingOsmFallback = true;
                attachTileLayer();
                showToast('Switched to fallback street map tiles.', 'info');
            }
        });

        state.tileLayer.addTo(state.map);
    }

    function buildSharerDivIcon() {
        return L.divIcon({
            className: 'custom-marker',
            html: '<div class="marker-pin-outer"><div class="marker-direction-arrow is-hidden"></div><div class="marker-pin-inner"></div><div class="marker-pulse-ring"></div></div>',
            iconSize: [30, 30],
            iconAnchor: [15, 15]
        });
    }

    function updateMarkerHeading(marker, heading) {
        if (!marker) return;
        const elem = marker.getElement();
        if (!elem) return;
        const arrow = elem.querySelector('.marker-direction-arrow');
        if (!arrow) return;
        if (Number.isFinite(heading)) {
            arrow.classList.remove('is-hidden');
            arrow.style.transform = `rotate(${heading}deg)`;
        } else {
            arrow.classList.add('is-hidden');
        }
    }

    function animateMarkerTo(key, marker, targetLatLng, onFrame) {
        if (!marker) return;
        const reduceMotion = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
        const from = marker.getLatLng();
        if (reduceMotion || !from || (from.lat === targetLatLng[0] && from.lng === targetLatLng[1])) {
            marker.setLatLng(targetLatLng);
            if (onFrame) onFrame(L.latLng(targetLatLng));
            return;
        }

        if (state.markerAnimations[key]) {
            cancelAnimationFrame(state.markerAnimations[key]);
        }

        const startTime = performance.now();
        const duration = 450;
        const startLat = from.lat;
        const startLng = from.lng;
        const dLat = targetLatLng[0] - startLat;
        const dLng = targetLatLng[1] - startLng;

        const tick = (now) => {
            const t = Math.min(1, (now - startTime) / duration);
            const eased = 1 - Math.pow(1 - t, 3);
            const cur = [startLat + dLat * eased, startLng + dLng * eased];
            marker.setLatLng(cur);
            if (onFrame) onFrame(cur);
            if (t < 1) {
                state.markerAnimations[key] = requestAnimationFrame(tick);
            } else {
                delete state.markerAnimations[key];
            }
        };

        state.markerAnimations[key] = requestAnimationFrame(tick);
    }

    function upsertPrecisionCircle(latlng, accuracy) {
        if (!state.map) return;
        const radius = Math.max(5, Math.min(5000, accuracy || 20));
        if (!state.sharerAccuracyCircle) {
            state.sharerAccuracyCircle = L.circle(latlng, {
                radius,
                color: '#6366f1',
                fillColor: '#6366f1',
                fillOpacity: 0.12,
                weight: 1.5,
                opacity: 0.45,
                interactive: false
            }).addTo(state.map);
        } else {
            state.sharerAccuracyCircle.setLatLng(latlng);
            state.sharerAccuracyCircle.setRadius(radius);
        }
    }

    function updateSharerMap(coords) {
        if (!state.map) return;
        const latlng = [coords.lat, coords.lng];

        if (!state.sharerMarker) {
            state.sharerMarker = L.marker(latlng, { icon: buildSharerDivIcon() }).addTo(state.map);
            state.breadcrumbsPolyline = L.polyline(state.coordsHistory, {
                color: '#6366f1',
                weight: 4,
                opacity: 0.85
            }).addTo(state.map);
            upsertPrecisionCircle(latlng, coords.acc);
            state.map.setView(latlng, 16);
        } else {
            animateMarkerTo('sharer', state.sharerMarker, latlng, (cur) => {
                if (state.sharerAccuracyCircle) state.sharerAccuracyCircle.setLatLng(cur);
            });
            upsertPrecisionCircle(latlng, coords.acc);
            if (state.breadcrumbsPolyline) {
                state.breadcrumbsPolyline.setLatLngs(state.coordsHistory);
            }
            if (state.autoFollow) {
                state.map.panTo(latlng, { animate: true, duration: 0.45 });
            }
        }
        updateMarkerHeading(state.sharerMarker, coords.dir);
    }

    function updateViewerMap(coords) {
        if (!state.map) return;
        const latlng = [coords.lat, coords.lng];

        if (!state.sharerMarker) {
            state.sharerMarker = L.marker(latlng, { icon: buildSharerDivIcon() }).addTo(state.map);
            state.breadcrumbsPolyline = L.polyline(state.viewer.history, {
                color: '#6366f1',
                weight: 4,
                opacity: 0.85,
                dashArray: '6, 8'
            }).addTo(state.map);
            upsertPrecisionCircle(latlng, coords.acc);
            state.map.setView(latlng, 16);
        } else {
            animateMarkerTo('viewer-sharer', state.sharerMarker, latlng, (cur) => {
                if (state.sharerAccuracyCircle) state.sharerAccuracyCircle.setLatLng(cur);
            });
            upsertPrecisionCircle(latlng, coords.acc);
            if (state.breadcrumbsPolyline) {
                state.breadcrumbsPolyline.setLatLngs(state.viewer.history);
            }
            if (state.autoFollow) {
                state.map.panTo(latlng, { animate: true, duration: 0.45 });
            }
        }
        updateMarkerHeading(state.sharerMarker, coords.dir);
    }

    function resetMapLayers() {
        Object.values(state.markerAnimations).forEach((id) => cancelAnimationFrame(id));
        state.markerAnimations = {};
        if (state.map) {
            [state.sharerMarker, state.sharerAccuracyCircle, state.viewerMarker, state.breadcrumbsPolyline].forEach((layer) => {
                if (layer) state.map.removeLayer(layer);
            });
        }
        state.sharerMarker = null;
        state.sharerAccuracyCircle = null;
        state.viewerMarker = null;
        state.breadcrumbsPolyline = null;
        state.coordsHistory = [];
        state.viewer.history = [];
    }

    function updateFollowButtonUI() {
        if (!el.btnRecenter || !el.recenterLabel) return;
        if (state.autoFollow) {
            el.btnRecenter.classList.add('is-following');
            el.recenterLabel.innerText = 'Following Live';
        } else {
            el.btnRecenter.classList.remove('is-following');
            el.recenterLabel.innerText = 'Center on User';
        }
    }

    function recenterMapOnSharer() {
        state.autoFollow = true;
        updateFollowButtonUI();

        if (state.mode === 'viewer' && state.viewer.coords) {
            const zoom = Math.max(16, state.map.getZoom());
            state.map.setView([state.viewer.coords.lat, state.viewer.coords.lng], zoom, { animate: true });
        } else if (state.mode === 'sharing' && state.lastCoords) {
            const zoom = Math.max(16, state.map.getZoom());
            state.map.setView([state.lastCoords.lat, state.lastCoords.lng], zoom, { animate: true });
        } else {
            showToast('Waiting for initial GPS fix...', 'warning');
        }
    }

    // Viewer Own Location (Distance Calculation)
    function toggleViewerLocation() {
        if (state.viewer.myWatchId !== null) {
            navigator.geolocation.clearWatch(state.viewer.myWatchId);
            state.viewer.myWatchId = null;
            state.viewer.myCoords = null;
            if (state.viewerMarker && state.map) {
                state.map.removeLayer(state.viewerMarker);
                state.viewerMarker = null;
            }
            el.btnToggleMyLocation.querySelector('span').innerText = 'Show my location to measure distance';
            el.viewStatDistance.innerText = '--';
            showToast('Hidden your own location.', 'info');
            return;
        }

        if (!navigator.geolocation) {
            showToast('Geolocation is not supported by your browser.', 'error');
            return;
        }

        el.btnToggleMyLocation.querySelector('span').innerText = 'Acquiring your location...';

        state.viewer.myWatchId = navigator.geolocation.watchPosition(
            (pos) => {
                const lat = pos.coords.latitude;
                const lng = pos.coords.longitude;
                state.viewer.myCoords = { lat, lng };
                el.btnToggleMyLocation.querySelector('span').innerText = 'Hide my location';

                const latlng = [lat, lng];
                if (!state.viewerMarker && state.map) {
                    const viewerIcon = L.divIcon({
                        className: 'custom-viewer-marker',
                        html: '<div class="viewer-marker-pin-outer"><div class="viewer-marker-pin-inner"></div></div>',
                        iconSize: [24, 24],
                        iconAnchor: [12, 12]
                    });
                    state.viewerMarker = L.marker(latlng, { icon: viewerIcon }).addTo(state.map);
                } else if (state.viewerMarker) {
                    state.viewerMarker.setLatLng(latlng);
                }

                updateDistanceUI();
            },
            (err) => {
                if (err.code === 1) {
                    const env = Geo.detectBrowserGeoEnvironment();
                    showToast(`Location blocked in ${env.browserName}. Allow location to measure distance.`, 'warning');
                } else {
                    showToast('Could not read your location right now.', 'warning');
                }
                if (state.viewer.myWatchId !== null) {
                    navigator.geolocation.clearWatch(state.viewer.myWatchId);
                    state.viewer.myWatchId = null;
                }
                el.btnToggleMyLocation.querySelector('span').innerText = 'Show my location to measure distance';
            },
            { enableHighAccuracy: false, maximumAge: 15000, timeout: 12000 }
        );
    }

    function updateDistanceUI() {
        if (state.viewer.coords && state.viewer.myCoords) {
            const meters = Geo.calculateHaversineMeters(state.viewer.coords, state.viewer.myCoords);
            el.viewStatDistance.innerText = Geo.formatDistance(meters);
        } else {
            el.viewStatDistance.innerText = '--';
        }
    }

    function openDirections() {
        if (state.mode === 'viewer' && state.viewer.coords) {
            const { lat, lng } = state.viewer.coords;
            window.open(`https://www.google.com/maps/dir/?api=1&destination=${lat},${lng}`, '_blank', 'noopener');
        } else {
            showToast('Destination coordinates not received yet.', 'warning');
        }
    }

    // --- TIMERS & STATUS ---

    function updateCountdownTimers() {
        const now = Date.now();

        if (state.mode === 'sharing' && state.activeShare) {
            const remaining = state.activeShare.exp - now;
            if (remaining <= 0) {
                el.sharingTimer.innerText = 'Expired';
                stopLocationSharing(true);
            } else {
                el.sharingTimer.innerText = formatCountdown(remaining);
            }
        }

        if (state.mode === 'viewer' && !state.viewer.isEnded) {
            if (state.viewer.exp) {
                const remaining = state.viewer.exp - now;
                if (remaining <= 0) {
                    state.viewer.isEnded = true;
                    el.viewerTimer.innerText = 'Expired';
                    el.viewerStatusText.innerText = 'Session expired';
                    el.viewerPulse.className = 'pulse-dot red';
                    showToast('This location sharing session has expired.', 'warning');
                    if (state.sync) state.sync.stop();
                    return;
                }
                el.viewerTimer.innerText = formatCountdown(remaining);
            }

            if (state.viewer.lastPingTime) {
                const ageSec = Math.max(0, Math.floor((now - state.viewer.lastPingTime) / 1000));
                el.viewStatPing.innerText = ageSec < 3 ? 'Just now' : `${ageSec}s ago`;

                if (ageSec > 25) {
                    el.viewerStatusText.innerText = 'Weak Signal / Waiting...';
                    el.viewerPulse.className = 'pulse-dot amber';
                }
            }
        }
    }

    function formatCountdown(ms) {
        if (ms <= 0) return 'Expired';
        const totalSecs = Math.floor(ms / 1000);
        const hours = Math.floor(totalSecs / 3600);
        const minutes = Math.floor((totalSecs % 3600) / 60);
        const seconds = totalSecs % 60;
        const pad = (n) => String(n).padStart(2, '0');
        return hours > 0
            ? `${pad(hours)}:${pad(minutes)}:${pad(seconds)}`
            : `${pad(minutes)}:${pad(seconds)}`;
    }

    function updateNetworkStatus(status, text) {
        el.networkStatusText.innerText = text;
        let iconName = 'wifi-off';
        let colorCls = 'danger';

        if (status === 'connected') {
            iconName = 'wifi';
            colorCls = 'green';
        } else if (status === 'connecting') {
            iconName = 'radio';
            colorCls = 'warning';
        }

        if (el.wifiIconWrap) {
            el.wifiIconWrap.className = `status-icon ${colorCls}`;
            if (el.wifiIconWrap.getAttribute('data-icon') !== iconName) {
                el.wifiIconWrap.setAttribute('data-icon', iconName);
                el.wifiIconWrap.innerHTML = `<i data-lucide="${iconName}" aria-hidden="true"></i>`;
                if (window.lucide) {
                    lucide.createIcons();
                }
            }
        }
    }

    // --- COPY, SHARE, TOASTS & HELPERS ---

    let copyResetTimer = null;
    let lastCopyMessage = '';

    function legacyCopy(text) {
        const field = document.createElement('textarea');
        field.value = text;
        field.setAttribute('readonly', '');
        field.style.cssText = 'position:fixed;inset-block-start:0;opacity:0';
        document.body.append(field);
        field.select();
        try {
            return document.execCommand('copy');
        } finally {
            field.remove();
        }
    }

    function reportCopyFeedback(ok) {
        const copyIcon = el.btnCopyLink.querySelector('.copy-default');
        const successIcon = el.btnCopyLink.querySelector('.copy-success');
        if (copyResetTimer) clearTimeout(copyResetTimer);

        el.btnCopyLink.removeAttribute('data-copied');
        el.btnCopyLink.removeAttribute('data-failed');
        el.copyStatusTip.textContent = '';
        void el.btnCopyLink.offsetWidth;

        let message = ok ? 'Copied' : 'Copy failed';
        if (message === lastCopyMessage) message += '\u00A0';
        lastCopyMessage = message;

        el.btnCopyLink.setAttribute(ok ? 'data-copied' : 'data-failed', '');
        requestAnimationFrame(() => {
            el.copyStatusTip.textContent = message;
        });

        if (ok && copyIcon && successIcon) {
            copyIcon.classList.add('hidden');
            successIcon.classList.remove('hidden');
            showToast('Encrypted tracking link copied!', 'success');
        } else if (!ok) {
            showToast('Could not copy automatically. Copy the link box manually.', 'warning');
        }

        copyResetTimer = setTimeout(() => {
            el.btnCopyLink.removeAttribute('data-copied');
            el.btnCopyLink.removeAttribute('data-failed');
            el.copyStatusTip.textContent = '';
            if (copyIcon && successIcon) {
                copyIcon.classList.remove('hidden');
                successIcon.classList.add('hidden');
            }
        }, 2000);
    }

    async function copyShareLink() {
        const shareUrl = el.shareUrlInput.value;
        if (!shareUrl) return;
        try {
            await navigator.clipboard.writeText(shareUrl);
            reportCopyFeedback(true);
        } catch {
            try {
                if (legacyCopy(shareUrl)) {
                    reportCopyFeedback(true);
                    return;
                }
            } catch { /* ignore */ }
            reportCopyFeedback(false);
        }
    }

    function shareViaApi() {
        const shareUrl = el.shareUrlInput.value;
        if (!shareUrl) return;

        if (navigator.share) {
            navigator.share({
                title: 'P-Near - Live Location',
                text: 'Track my live location on P-Near:',
                url: shareUrl
            }).catch(() => {});
        } else {
            copyShareLink();
        }
    }

    function showToast(message, type) {
        const kind = type || 'info';
        const toast = document.createElement('div');
        toast.className = `toast ${kind}`;

        let iconName = 'info';
        if (kind === 'success') iconName = 'check-circle';
        if (kind === 'warning') iconName = 'alert-triangle';
        if (kind === 'error') iconName = 'x-circle';

        const iconEl = document.createElement('i');
        iconEl.setAttribute('data-lucide', iconName);
        iconEl.setAttribute('aria-hidden', 'true');

        const spanEl = document.createElement('span');
        spanEl.textContent = message;

        toast.append(iconEl, spanEl);
        el.toastContainer.appendChild(toast);

        if (window.lucide) {
            lucide.createIcons({ attrs: { class: 'toast-icon' } });
        }

        setTimeout(() => {
            toast.classList.add('removing');
            setTimeout(() => toast.remove(), 300);
        }, 4200);
    }

    function showLoader(text) {
        el.loaderText.innerText = text;
        el.globalLoader.classList.remove('hidden');
    }

    function hideLoader() {
        el.globalLoader.classList.add('hidden');
    }

    function generateRandomId(length) {
        const chars = 'abcdefghijklmnopqrstuvwxyz0123456789';
        let result = '';
        if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
            const bytes = new Uint8Array(length);
            crypto.getRandomValues(bytes);
            for (let i = 0; i < length; i++) {
                result += chars.charAt(bytes[i] % chars.length);
            }
            return result;
        }
        for (let i = 0; i < length; i++) {
            result += chars.charAt(Math.floor(Math.random() * chars.length));
        }
        return result;
    }
})();
