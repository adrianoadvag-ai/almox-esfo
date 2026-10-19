// Service worker do Almox EsFO: permite instalar o app na tela inicial e exibir avisos.
// Versão 2: NÃO intercepta conexões de outros endereços (Firebase, Google, fontes).
// A versão anterior repassava todas as conexões, o que travava o banco de dados no Safari do iPhone.
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', e => e.waitUntil(self.clients.claim()));
self.addEventListener('fetch', e => {
  const req = e.request;
  // Só a abertura da própria página passa por aqui; todo o resto segue direto pela internet.
  if (req.mode !== 'navigate' || new URL(req.url).origin !== self.location.origin) return;
  e.respondWith(fetch(req).catch(() => new Response(
    '<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">' +
    '<body style="font-family:system-ui;padding:2rem;text-align:center"><h2>Almox EsFO</h2><p>Sem conexão com a internet.</p>' +
    '<p><button onclick="location.reload()">Tentar de novo</button></p></body>',
    { headers: { 'Content-Type': 'text/html; charset=utf-8' } })));
});
self.addEventListener('notificationclick', e => {
  e.notification.close();
  e.waitUntil(self.clients.matchAll({ type: 'window', includeUncontrolled: true }).then(list => {
    for (const c of list) { if ('focus' in c) return c.focus(); }
    return self.clients.openWindow('./');
  }));
});
