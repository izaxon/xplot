const CACHE = 'xplot-v1.1.0';

self.addEventListener('install', (event) => {
   event.waitUntil(
      caches.open(CACHE).then((cache) => cache.addAll(['./', './index.html', './manifest.webmanifest', './favicon.png']))
         .then(() => self.skipWaiting())
   );
});

self.addEventListener('activate', (event) => {
   event.waitUntil(
      caches.keys()
         .then((keys) => Promise.all(keys.filter((key) => key !== CACHE).map((key) => caches.delete(key))))
         .then(() => self.clients.claim())
   );
});

self.addEventListener('fetch', (event) => {
   const request = event.request;
   if (request.method !== 'GET') {
      return;
   }

   const url = new URL(request.url);
   if (url.origin !== self.location.origin) {
      return;
   }

   event.respondWith(
      fetch(request)
         .then((response) => {
            if (response.ok) {
               const copy = response.clone();
               caches.open(CACHE).then((cache) => cache.put(request, copy));
            }
            return response;
         })
         .catch(() => caches.match(request))
   );
});
