# Almox EsFO

Sistema de cautela de materiais do almoxarifado da Escola de Formação de Oficiais (APMG/PMPR).
Mesma base, identidade visual, cadastro e assinatura do SICAM.

- **App:** https://adrianoadvag-ai.github.io/almox-esfo/
- **Firebase:** projeto `almox-esfo` (plano Spark, Firestore em São Paulo)
- **Regras do banco:** `firestore.rules` (copiar em Firebase → Firestore → Regras → Publicar)

## Fluxo
1. Cadete/oficial cria a conta com o e-mail @pm.pr.gov.br, preenche o romaneio e confirma o e-mail.
2. O almoxarifado libera o acesso.
3. Pedido pelo app (tamanho sugerido pelo romaneio) → almoxarifado separa (prazo opcional) → militar assina no celular (senha ou digital/Face ID) → almoxarifado confirma a entrega.
4. No balcão: o almoxarife monta a cautela e o militar assina com a senha no aparelho do almoxarifado ou no próprio celular.
5. Transferência entre militares: quem entrega assina, quem recebe aceita e assina (sem homologação).
6. Devolução total ou parcial, com registro de dano/extravio.

Arquivos: `index.html`, `app.js` (todo o sistema), `style.css`, `config.js` (ligação com o Firebase), `sw.js`, `manifest.json`.
