// P-Near Minimal Service Worker (PWA Installability + Instant Network Freshness)
self.addEventListener('install', () => {
    self.skipWaiting();
});

self.addEventListener('activate', (event) => {
    event.waitUntil(self.clients.claim());
});

self.addEventListener('fetch', () => {
    // Pass through to network so real-time shares and map tiles stay fresh
});
