/**
 * P-Near Geolocation & Trajectory Engine (v3 - by Parot)
 * - Single gesture-authorized watchPosition (never destroys & recreates watch asynchronously on Safari/iOS)
 * - Active 3-second live polling fallback so mobile & desktop continuously stream coordinates
 * - Seamless High-Accuracy <-> WiFi/CoreLocation fallback for laptops without throwing spurious errors
 * - Outlier/teleportation rejection, stationary jitter damping, bearing & ground-speed smoothing
 */
(function (global) {
    'use strict';

    const GEO_CONFIG = {
        PRIMARY_WATCH_OPTS: { enableHighAccuracy: true, maximumAge: 5000, timeout: 20000 },
        COARSE_WATCH_OPTS: { enableHighAccuracy: false, maximumAge: 10000, timeout: 15000 },
        POLL_INTERVAL_MS: 3000,
        POLL_STALE_THRESHOLD_MS: 3200,
        REUPGRADE_INTERVAL_MS: 45000,
        MAX_TELEPORT_SPEED_MS: 350, // ~1260 km/h safety cap
        FRESH_FIX_WINDOW_MS: 20000
    };

    function toRad(deg) {
        return deg * Math.PI / 180;
    }

    function toDeg(rad) {
        return rad * 180 / Math.PI;
    }

    function calculateHaversineMeters(a, b) {
        if (!a || !b) return 0;
        const R = 6371000;
        const dLat = toRad(b.lat - a.lat);
        const dLng = toRad(b.lng - a.lng);
        const lat1 = toRad(a.lat);
        const lat2 = toRad(b.lat);
        const sinLat = Math.sin(dLat / 2);
        const sinLng = Math.sin(dLng / 2);
        const h = sinLat * sinLat + Math.cos(lat1) * Math.cos(lat2) * sinLng * sinLng;
        return 2 * R * Math.atan2(Math.sqrt(h), Math.sqrt(1 - h));
    }

    function formatDistance(meters) {
        if (!Number.isFinite(meters) || meters < 0) return '--';
        if (meters < 1000) return `${Math.round(meters)} m`;
        return `${(meters / 1000).toFixed(2)} km`;
    }

    function calculateBearingDeg(from, to) {
        if (!from || !to) return null;
        const lat1 = toRad(from.lat);
        const lat2 = toRad(to.lat);
        const dLng = toRad(to.lng - from.lng);
        const y = Math.sin(dLng) * Math.cos(lat2);
        const x = Math.cos(lat1) * Math.sin(lat2) - Math.sin(lat1) * Math.cos(lat2) * Math.cos(dLng);
        return (toDeg(Math.atan2(y, x)) + 360) % 360;
    }

    function getAccuracyQuality(meters) {
        if (!Number.isFinite(meters)) return { tier: 'unknown', label: 'Unknown' };
        if (meters <= 20) return { tier: 'excellent', label: 'High GPS' };
        if (meters <= 65) return { tier: 'good', label: 'Good' };
        if (meters <= 200) return { tier: 'fair', label: 'WiFi/Cell' };
        return { tier: 'coarse', label: 'Approx' };
    }

    function detectBrowserGeoEnvironment() {
        const ua = (typeof navigator !== 'undefined' && navigator.userAgent) ? navigator.userAgent : '';
        const isIOS = /iPhone|iPad|iPod/i.test(ua) || (typeof navigator !== 'undefined' && navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
        const isMac = /Macintosh|Mac OS X/i.test(ua) && !isIOS;
        const isAndroid = /Android/i.test(ua);
        const isSafari = /Safari/i.test(ua) && !/Chrome|CriOS|FxiOS|Edg|OPR|Brave/i.test(ua);
        const isBrave = Boolean(typeof navigator !== 'undefined' && navigator.brave);
        const isFirefox = /Firefox|FxiOS/i.test(ua);

        let browserName = 'your browser';
        let steps = 'Click the location/lock icon in the address bar, set Location to Allow, then click Retry GPS.';

        if (isIOS && isSafari) {
            browserName = 'iOS Safari';
            steps = 'Open iOS Settings > Privacy & Security > Location Services > Safari Websites -> "While Using the App", or tap "aA" in Safari address bar -> Website Settings -> Location: Allow.';
        } else if (isMac && isSafari) {
            browserName = 'macOS Safari';
            steps = '1) Safari > Settings > Websites > Location -> Allow for near.parotcorp.com. 2) System Settings > Privacy & Security > Location Services -> Enable Safari.';
        } else if (isBrave) {
            browserName = 'Brave';
            steps = 'Click the lock/location icon in the address bar -> Location: Allow.';
        } else if (isFirefox) {
            browserName = 'Firefox';
            steps = 'Click the lock/location icon in the address bar, clear Blocked Location, and click Retry GPS.';
        } else if (isAndroid) {
            browserName = 'Android Browser';
            steps = 'Tap the lock/tune icon next to the URL -> Permissions -> Location: Allow, and ensure phone GPS is turned ON.';
        } else {
            browserName = 'Browser';
        }

        return { isIOS, isMac, isAndroid, isSafari, isBrave, isFirefox, browserName, steps };
    }

    async function queryGeoPermissionState() {
        try {
            if (typeof navigator === 'undefined' || !navigator.permissions || !navigator.permissions.query) {
                return 'unknown';
            }
            const status = await navigator.permissions.query({ name: 'geolocation' });
            return status.state || 'unknown';
        } catch {
            return 'unknown';
        }
    }

    /**
     * Filters incoming GeolocationPosition against prior accepted state.
     * Returns { accepted: boolean, reason?: string, coordObj?: object, addedDistanceMeters: number }
     */
    function processGpsReading(position, trackerState) {
        if (!position || !position.coords) {
            return { accepted: false, reason: 'missing-coords', addedDistanceMeters: 0 };
        }

        const c = position.coords;
        const lat = Number(c.latitude);
        const lng = Number(c.longitude);
        const accuracy = Number.isFinite(c.accuracy) && c.accuracy > 0 ? Math.round(c.accuracy) : 50;

        if (!Number.isFinite(lat) || !Number.isFinite(lng) || lat < -90 || lat > 90 || lng < -180 || lng > 180) {
            return { accepted: false, reason: 'invalid-latlng', addedDistanceMeters: 0 };
        }

        const prev = trackerState.lastCoords;
        const rawTs = Number.isFinite(position.timestamp) && position.timestamp > 0 ? position.timestamp : Date.now();
        const now = prev && rawTs <= prev.time ? Date.now() : rawTs;
        let distFromPrev = 0;
        let addedDistanceMeters = 0;

        if (prev) {
            const dtMs = Math.max(100, now - prev.time);
            const dtSec = dtMs / 1000;
            distFromPrev = calculateHaversineMeters(prev, { lat, lng });

            // 1. Reject coarse WiFi/IP noise while we still have a fresh, significantly sharper fix
            const isUpgradingPrecision = accuracy <= prev.acc;
            if (!isUpgradingPrecision && prev.acc <= 80 && accuracy > 280 && dtMs < GEO_CONFIG.FRESH_FIX_WINDOW_MS) {
                return { accepted: false, reason: 'coarse-outlier', addedDistanceMeters: 0 };
            }

            // 2. Reject physically impossible jumps when both fixes have reasonable precision
            const impliedSpeedMs = distFromPrev / dtSec;
            if (dtSec < 8 && impliedSpeedMs > GEO_CONFIG.MAX_TELEPORT_SPEED_MS && prev.acc <= 150 && accuracy <= 150) {
                return { accepted: false, reason: 'teleport-spike', addedDistanceMeters: 0 };
            }

            // Accumulate traveled distance only when move exceeds noise threshold
            const noiseThreshold = Math.max(3, Math.min(25, accuracy * 0.25));
            if (distFromPrev >= noiseThreshold && dtSec >= 0.4) {
                addedDistanceMeters = distFromPrev;
            }
        }

        // Resolve speed (km/h): prefer hardware speed when finite & non-negative, else compute smoothed displacement
        let speedKmh = 0;
        if (Number.isFinite(c.speed) && c.speed >= 0) {
            speedKmh = Math.round(c.speed * 3.6);
        } else if (prev) {
            const dtSec = (now - prev.time) / 1000;
            const moveThreshold = Math.max(4, Math.min(20, accuracy * 0.2));
            if (dtSec >= 1.2 && distFromPrev >= moveThreshold) {
                const rawKmh = (distFromPrev / dtSec) * 3.6;
                speedKmh = rawKmh <= 450 ? Math.round(rawKmh) : (prev.spd || 0);
            }
        }

        // Resolve bearing: prefer native finite heading, otherwise derive from displacement >= 3m
        let heading = null;
        if (Number.isFinite(c.heading) && c.heading >= 0 && c.heading <= 360) {
            heading = Math.round(c.heading);
        } else if (prev && distFromPrev >= 3) {
            heading = Math.round(calculateBearingDeg(prev, { lat, lng }));
        } else if (prev && Number.isFinite(prev.dir)) {
            heading = prev.dir;
        }

        const coordObj = {
            lat: Number(lat.toFixed(6)),
            lng: Number(lng.toFixed(6)),
            acc: accuracy,
            spd: speedKmh,
            dir: heading,
            alt: Number.isFinite(c.altitude) ? Math.round(c.altitude) : null,
            time: now
        };

        return {
            accepted: true,
            coordObj,
            addedDistanceMeters,
            quality: getAccuracyQuality(accuracy)
        };
    }

    /**
     * Single-Watch + Active 3-Second Live Poller.
     * Never breaks iOS/macOS Safari user gesture by destroying/recreating watch after first fix.
     */
    class AdaptiveGeoTracker {
        constructor(callbacks) {
            this.callbacks = callbacks || {};
            this.watchId = null;
            this.pollTimer = null;
            this.mode = 'idle'; // 'idle' | 'high' | 'network' | 'denied' | 'stopped'
            this.receivedFirstFix = false;
            this.lastFixWallTime = 0;
            this.highAccFailures = 0;
            this.coarseFailures = 0;
            this.pollInFlight = false;
            this.generation = 0;
        }

        /**
         * MUST be called synchronously inside a user-click gesture on start/retry.
         */
        startSync() {
            if (typeof navigator === 'undefined' || !navigator.geolocation) {
                this._emitError('unsupported', { message: 'Geolocation is not supported by your browser.' });
                return;
            }

            this.stop();
            this.generation++;
            this.receivedFirstFix = false;
            this.lastFixWallTime = 0;
            this.highAccFailures = 0;
            this.coarseFailures = 0;
            this.pollInFlight = false;

            // Keep ONE watchPosition directly from the click gesture (critical for Safari/iOS live updates)
            this._startWatch(GEO_CONFIG.PRIMARY_WATCH_OPTS, 'high');
            this._startActivePoller();
        }

        stop() {
            this.generation++;
            if (this.watchId !== null && typeof navigator !== 'undefined' && navigator.geolocation) {
                navigator.geolocation.clearWatch(this.watchId);
                this.watchId = null;
            }
            if (this.pollTimer) {
                clearInterval(this.pollTimer);
                this.pollTimer = null;
            }
            this.pollInFlight = false;
            this.mode = 'stopped';
        }

        _startWatch(options, targetMode) {
            const gen = this.generation;
            if (this.watchId !== null) {
                navigator.geolocation.clearWatch(this.watchId);
                this.watchId = null;
            }
            this.mode = targetMode;

            if (this.callbacks.onModeChange) {
                this.callbacks.onModeChange(targetMode);
            }

            this.watchId = navigator.geolocation.watchPosition(
                (pos) => {
                    if (gen !== this.generation) return;
                    this._deliverPosition(pos, this.mode);
                },
                (err) => {
                    if (gen !== this.generation) return;
                    this._handleError(err);
                },
                options
            );
        }

        _deliverPosition(pos, sourceMode) {
            const wasFirst = !this.receivedFirstFix;
            this.receivedFirstFix = true;
            this.lastFixWallTime = Date.now();
            this.highAccFailures = 0;
            this.coarseFailures = 0;

            if (this.callbacks.onPosition) {
                this.callbacks.onPosition(pos, { mode: sourceMode, isFirstFix: wasFirst });
            }
        }

        _startActivePoller() {
            if (this.pollTimer) clearInterval(this.pollTimer);
            const gen = this.generation;

            this.pollTimer = setInterval(() => {
                if (gen !== this.generation || this.mode === 'stopped' || this.mode === 'denied') return;
                if (typeof navigator === 'undefined' || !navigator.geolocation) return;
                // Wait until permission/first watch settles or stale >= 3.2s
                if (!this.receivedFirstFix || this.pollInFlight) return;
                if (Date.now() - this.lastFixWallTime < GEO_CONFIG.POLL_STALE_THRESHOLD_MS) return;

                this.pollInFlight = true;
                const opts = this.mode === 'network'
                    ? { enableHighAccuracy: false, maximumAge: 5000, timeout: 9000 }
                    : { enableHighAccuracy: true, maximumAge: 3000, timeout: 9000 };

                navigator.geolocation.getCurrentPosition(
                    (pos) => {
                        this.pollInFlight = false;
                        if (gen !== this.generation) return;
                        this._deliverPosition(pos, this.mode);
                    },
                    (err) => {
                        this.pollInFlight = false;
                        if (gen !== this.generation) return;
                        if (err && err.code === 1) {
                            this._handleError(err);
                        } else if (this.mode === 'high' && err && (err.code === 2 || err.code === 3)) {
                            this.highAccFailures++;
                            if (this.highAccFailures >= 3) {
                                this._downgradeToNetwork();
                            }
                        }
                    },
                    opts
                );
            }, GEO_CONFIG.POLL_INTERVAL_MS);
        }

        _handleError(err) {
            const code = err ? err.code : 0;
            if (code === 1) { // PERMISSION_DENIED
                this.stop();
                this.mode = 'denied';
                this._emitError('denied', err);
                return;
            }

            if (code === 2 || code === 3) { // POSITION_UNAVAILABLE or TIMEOUT
                if (this.mode === 'high') {
                    this.highAccFailures++;
                    // Quickly fall back to WiFi/CoreLocation on laptops without scary errors
                    if (this.highAccFailures >= 1 && !this.receivedFirstFix) {
                        this._downgradeToNetwork();
                        return;
                    }
                    if (this.highAccFailures >= 3) {
                        this._downgradeToNetwork();
                        return;
                    }
                    if (!this.receivedFirstFix && this.callbacks.onStatus) {
                        this.callbacks.onStatus('acquiring', 'Acquiring signal...');
                    }
                    return;
                }

                // Already in network mode
                this.coarseFailures++;
                if (this.coarseFailures >= 3 && !this.receivedFirstFix) {
                    this._emitError('unavailable', err);
                } else if (!this.receivedFirstFix && this.callbacks.onStatus) {
                    this.callbacks.onStatus('network', 'Using WiFi positioning...');
                }
                return;
            }

            if (!this.receivedFirstFix && this.callbacks.onStatus) {
                this.callbacks.onStatus('acquiring', 'Acquiring signal...');
            }
        }

        _downgradeToNetwork() {
            this._startWatch(GEO_CONFIG.COARSE_WATCH_OPTS, 'network');
            if (!this.receivedFirstFix && this.callbacks.onStatus) {
                this.callbacks.onStatus('network', 'Using WiFi positioning...');
            }
        }

        _emitError(kind, rawErr) {
            if (this.callbacks.onError) {
                this.callbacks.onError(kind, rawErr, detectBrowserGeoEnvironment());
            }
        }
    }

    const exported = {
        GEO_CONFIG,
        calculateHaversineMeters,
        formatDistance,
        calculateBearingDeg,
        getAccuracyQuality,
        detectBrowserGeoEnvironment,
        queryGeoPermissionState,
        processGpsReading,
        AdaptiveGeoTracker
    };

    if (typeof module !== 'undefined' && module.exports) {
        module.exports = exported;
    } else {
        global.PNearGeo = exported;
    }
})(typeof window !== 'undefined' ? window : globalThis);
