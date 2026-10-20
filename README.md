# Almox EsFO

Sistema de cautela de materiais do almoxarifado da Escola de Formação de Oficiais (APMG/PMPR).
Mesma base, identidade visual, cadastro e assinatura do SICAM.

- **App:** https://adrianoadvag-ai.github.io/almox-esfo/
- **Firebase:** projeto `almox-esfo` (plano Spark, Firestore em São Paulo)
- **Regras do banco:** `firestore.rules` (copiar em Firebase → Firestore → Regras → Publicar)

- **Política de privacidade (LGPD):** `privacidade.html` – ao mudar o texto, mude `PRIV_VER` em `app.js` para pedir o aceite de novo.

## Fluxo
1. Cadete/oficial cria a conta com o e-mail @pm.pr.gov.br (Companhia, turma, pelotão, CPF, RG, telefone), aceita a política de privacidade e confirma o e-mail.
2. O almoxarifado libera o acesso. O romaneio é preenchido depois, em "Meus dados".
3. Pedido pelo app: só aparece o que tem estoque livre; as peças pedidas ficam **reservadas** até a separação. Se algo faltar na hora de separar, o gestor separa o resto e o militar é avisado do que não foi atendido.
4. Entrega: o militar assina no celular (senha ou digital/Face ID) e o **gestor assina com a senha dele**.
5. Transferência entre militares: lista "Selecione o cadete…" agrupada por Companhia (como no SICAM); quem entrega assina, quem recebe aceita e assina.
6. Devolução: o militar pode **pedir pelo app** (assina o pedido); no balcão o gestor confere e assina. Se a conferência bater com o pedido, a assinatura do militar no pedido vale; se houver diferença, o militar assina de novo. Dano/extravio ficam registrados.

## Gestores do almoxarifado
- Cada gestor tem **conta própria por usuário** (sem e-mail), separada da conta de cadete dele.
- O **gestor principal** (quem fez a configuração inicial, ou quem ele indicar) gera um **código de convite** (24 h, uso único) em Militares → nome do cadete → "Convidar para gestor do almoxarifado". A pessoa cria a conta em "Acesso restrito do almoxarifado → Criar conta com convite".
- A conta de gestor fica **vinculada** à conta de cadete: o gestor não separa, entrega nem recebe devolução das próprias cautelas (o banco de dados também bloqueia).
- Esqueceu a senha de gestor: o principal desativa a conta antiga e gera um novo convite.

Arquivos: `index.html`, `app.js` (todo o sistema), `style.css`, `config.js` (ligação com o Firebase), `sw.js`, `manifest.json`.
