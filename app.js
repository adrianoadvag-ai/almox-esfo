import { initializeApp, deleteApp } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js';
import { getAuth, initializeAuth, inMemoryPersistence, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword,
signOut, reauthenticateWithCredential, EmailAuthProvider, updatePassword, sendEmailVerification, sendPasswordResetEmail } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js';
import { getFirestore, initializeFirestore, doc, getDoc, getDocs, setDoc, updateDoc, addDoc, collection, onSnapshot, writeBatch, runTransaction, query, where } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js';
import * as CFG from './config.js';

/* =====================================================================
   Almox EsFO – Sistema de cautela de materiais do almoxarifado da EsFO
   Base: SICAM (mesma identidade visual, cadastro e assinatura)
   ===================================================================== */
const VERSAO='1.4.2';
const FB=CFG.ALMOX_FIREBASE;
const DOMINIOS=((CFG.ALMOX_OPCOES&&CFG.ALMOX_OPCOES.dominios)||['pm.pr.gov.br']).map(d=>d.toLowerCase());
const $=s=>document.querySelector(s);
const $$=s=>[...document.querySelectorAll(s)];
const configurado=FB&&FB.apiKey&&!/COLE/i.test(FB.apiKey);
let app,auth,db;
let fase=configurado?'carregando':'naoconfig'; // naoconfig | carregando | setup | login | cadastro | verificar | aguardando | app | erro
let erroMsg='',loginMsg='';
const D0=()=>({users:[],cats:[],itens:[],cautelas:[],trfIn:[],dir:[],dirDoc:null,setup:null,eu:null});
let D=D0();
let sess=null,bootstrapping=false,unsubs=[],loaded={},aguardandoUnsub=null;
const ui={view:null,cart:[],cat:null,q:'',hq:'',mq:'',matQ:'',histTudo:false,cadTipo:'cadete'};
const baldes={ativas:[],recentes:[],tudo:[],minhas:[]};
const HIST_DIAS=90;

/* ============ Utilidades ============ */
/* Contas do almoxarifado podem usar um usuário (ex.: "almox"), como a Furrielação no SICAM: vira um e-mail interno, sem confirmação */
const DOMF='@almox.esfo';
const normLogin=s=>String(s||'').trim().toLowerCase().replace(/\s+/g,'');
const emailDe=x=>{const t=normLogin(x);return t.includes('@')?t:t+DOMF;};
const ehFicticio=email=>String(email||'').toLowerCase().endsWith(DOMF);
const dominioOk=email=>DOMINIOS.some(d=>String(email||'').toLowerCase().trim().endsWith('@'+d));
const b64u=buf=>{const b=new Uint8Array(buf);let t='';for(let i=0;i<b.length;i++)t+=String.fromCharCode(b[i]);return btoa(t).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,'');};
const ub64u=x=>{x=x.replace(/-/g,'+').replace(/_/g,'/');x+='='.repeat((4-x.length%4)%4);return Uint8Array.from(atob(x),c=>c.charCodeAt(0));};
const bioKey=uid=>'almox.bio.'+uid;
const bioLocal=uid=>{try{return localStorage.getItem(bioKey(uid));}catch(e){return null;}};
let bioOk=false;
(async()=>{try{bioOk=!!(window.PublicKeyCredential&&PublicKeyCredential.isUserVerifyingPlatformAuthenticatorAvailable&&await PublicKeyCredential.isUserVerifyingPlatformAuthenticatorAvailable());}catch(e){bioOk=false;}})();
const nowISO=()=>new Date().toISOString();
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt=iso=>{if(!iso)return'—';const d=new Date(iso);return d.toLocaleDateString('pt-BR',{day:'2-digit',month:'2-digit',year:'2-digit'})+' '+d.toLocaleTimeString('pt-BR',{hour:'2-digit',minute:'2-digit'});};
const fmtD=iso=>{if(!iso)return'—';const d=new Date(iso);return d.toLocaleDateString('pt-BR',{day:'2-digit',month:'2-digit',year:'numeric'});};
const dataInput=iso=>{if(!iso)return'';const d=new Date(iso),p=n=>String(n).padStart(2,'0');return d.getFullYear()+'-'+p(d.getMonth()+1)+'-'+p(d.getDate());};
const prazoDe=v=>v?new Date(v+'T23:59:00').toISOString():null;
const nr=n=>'Nº '+String(n||0).padStart(4,'0');
const norm=s=>String(s||'').normalize('NFD').replace(/[̀-ͯ]/g,'').toLowerCase();
const int=v=>{const n=parseInt(v,10);return isNaN(n)?0:n;};
const uidNovo=()=>Math.random().toString(36).slice(2,10)+Date.now().toString(36).slice(-4);

/* Romaneio: medidas do militar, usadas para sugerir o tamanho de cada item */
const ROM=[['gandola','Gandola / túnica (nº)'],['camisa','Camisa (tam.)'],['calca','Calça (nº)'],['calcado','Sapato / coturno (nº)'],
['cobertura','Cobertura – medida da cabeça'],['luva','Luva (tam.)'],['cinto','Cinto (tam.)']];
const ROMN=Object.fromEntries(ROM);
const ANOS=[['1','1º ano'],['2','2º ano'],['3','3º ano']];
const POSTOS=['Cel PM','Ten Cel PM','Maj PM','Cap PM','1º Ten PM','2º Ten PM','Asp Of PM'];
const UNID={un:['unidade','unidades'],par:['par','pares'],conj:['conjunto','conjuntos']};
const qtdU=(q,u)=>`${q} ${(UNID[u]||UNID.un)[q===1?0:1]}`;

/* Militares */
const me=()=>sess&&(D.users.find(u=>u.id===sess.userId)||D.eu);
const user=id=>D.users.find(u=>u.id===id)||D.dir.find(u=>u.id===id)||(D.eu&&D.eu.id===id?D.eu:null)||{nome:'?',guerra:'?',grad:''};
const nomeM=id=>{const u=user(id);return ((u.grad?u.grad+' ':'')+(u.guerra||u.nome||'?')).trim();};
const nomeU=u=>((u.grad?u.grad+' ':'')+(u.guerra||u.nome||'?')).trim();
const turmaU=u=>u.tipo==='oficial'?(u.opm||'Oficial'):[u.ano?u.ano+'º ano':'',u.pelotao||''].filter(Boolean).join(' · ');
const ehAlmox=()=>{const u=me();return !!u&&u.perfil==='almox';};

/* Catálogo */
const cat=id=>D.cats.find(c=>c.id===id)||{nome:'Sem categoria',ordem:999};
const item=id=>D.itens.find(i=>i.id===id)||{nome:'?',tamanhos:[],estoque:{},unidade:'un'};
const est=(it,t)=>((it.estoque||{})[t])||{total:0,disp:0};
const ordenarCats=a=>a.sort((x,y)=>(x.ordem||0)-(y.ordem||0)||String(x.nome).localeCompare(y.nome,'pt-BR'));
const ordenarItens=a=>a.sort((x,y)=>(cat(x.catId).ordem||0)-(cat(y.catId).ordem||0)||(x.ordem||0)-(y.ordem||0)||String(x.nome).localeCompare(y.nome,'pt-BR'));
const sugTam=(it,u)=>{if(!it.campo||!u||!u.romaneio)return '';const v=String(u.romaneio[it.campo]||'').trim();if(!v)return '';
const m=(it.tamanhos||[]).find(t=>norm(t)===norm(v));return m||'';};
const tamTxt=t=>!t||norm(t)==='unico'?'':t;

/* Cautelas */
const pend=l=>l.consumo?0:Math.max(0,(l.qtd||0)-(l.dev||0)-(l.trf||0));
const pendentes=c=>(c.itens||[]).filter(l=>pend(l)>0);
const atrasada=c=>c.status==='cautelada'&&!!c.prazo&&new Date(c.prazo)<new Date();
const ST={solicitada:['Solicitada','c-brass'],separada:['Pronta para retirada','c-blue'],cautelada:['Cautelado','c-ok'],devolvida:['Devolvida','c-muted'],
concluida:['Entregue','c-muted'],recusada:['Recusada','c-stamp'],cancelada:['Cancelada','c-muted'],transferida:['Transferida','c-muted']};
const stamp=(c,lg)=>{const k=lg?' lg':'';
if(c.status==='separada'&&c.assinatura)return `<span class="stamp c-ok${k}">Assinada</span>`;
if(atrasada(c))return `<span class="stamp c-stamp${k}">Em atraso</span>`;
if(c.status==='cautelada'&&c.transferPara)return `<span class="stamp c-brass${k}">Em transferência</span>`;
const s=ST[c.status]||[c.status,''];return `<span class="stamp ${s[1]}${k}">${s[0]}</span>`;};
const linhaTxt=l=>`${l.qtd}× ${l.nome}${tamTxt(l.tam)?' ('+l.tam+')':''}`;
const itensTxt=c=>(c.itens||[]).map(linhaTxt).join(', ');
const itensLi=(c,soPend)=>'<ul class="itens">'+(c.itens||[]).filter(l=>!soPend||pend(l)>0).map(l=>{
const extra=[];if(l.dev)extra.push(`${l.dev} devolvido${l.dev>1?'s':''}`);if(l.trf)extra.push(`${l.trf} transferido${l.trf>1?'s':''}`);if(l.consumo)extra.push('entrega definitiva');
return `<li><b>${soPend?pend(l):l.qtd}×</b><span>${esc(l.nome)}${tamTxt(l.tam)?` <span class="tag">${esc(l.tam)}</span>`:''}${extra.length?` <span class="small muted">(${extra.join(', ')})</span>`:''}</span></li>`;}).join('')+'</ul>';
const entrada=(a,obs)=>({t:nowISO(),a,por:sess.userId,obs:obs||''});
const C=id=>D.cautelas.find(c=>c.id===id)||D.trfIn.find(c=>c.id===id);

function toast(msg,bad){const t=document.createElement('div');t.className='toast'+(bad?' bad':'');t.textContent=msg;$('#toasts').appendChild(t);setTimeout(()=>t.remove(),5500);}
function erroFirebase(e){
const c=(e&&e.code)||'';
const m={'auth/invalid-credential':'E-mail ou senha incorretos.','auth/wrong-password':'E-mail ou senha incorretos.','auth/user-not-found':'E-mail ou senha incorretos.',
'auth/invalid-email':'E-mail inválido.','auth/too-many-requests':'Muitas tentativas. Aguarde alguns minutos e tente de novo.',
'auth/email-already-in-use':'Já existe uma conta com esse e-mail. Use "Entrar" ou "Esqueci minha senha".','auth/weak-password':'A senha precisa ter pelo menos 6 caracteres.',
'auth/network-request-failed':'Sem conexão com a internet.','permission-denied':'Sem permissão para essa ação. Confira se as regras do Firestore foram publicadas.',
'unavailable':'Sem conexão com o servidor. Tente de novo.','auth/operation-not-allowed':'O login por e-mail e senha não foi ativado no Firebase.',
'auth/requires-recent-login':'Por segurança, saia e entre de novo antes de trocar a senha.'};
return (e&&e.msg)||m[c]||('Erro: '+(e&&e.message||c||'desconhecido'));
}
async function avisar(titulo,corpo){
toast(titulo+(corpo?' – '+corpo:''));
try{navigator.vibrate&&navigator.vibrate(200);}catch(e){}
try{if('Notification' in window&&Notification.permission==='granted'&&document.hidden){
const reg=await navigator.serviceWorker?.getRegistration();if(reg)reg.showNotification(titulo,{body:corpo||'',icon:'icon-192.png',badge:'icon-192.png',tag:'almox'});}}catch(e){}
}

/* Aparência: Automático, Claro ou Escuro – guardada só neste aparelho */
const TEMAS=[['auto','Automático'],['light','Claro'],['dark','Escuro']];
let temaAtual='auto';try{temaAtual=localStorage.getItem('almox.tema')||'auto';}catch(e){}
function aplicarTema(t){const r=document.documentElement;if(t==='light'||t==='dark')r.setAttribute('data-theme',t);else r.removeAttribute('data-theme');
const escuro=t==='dark'||(t!=='light'&&window.matchMedia&&matchMedia('(prefers-color-scheme: dark)').matches);const m=document.querySelector('meta[name=theme-color]');if(m)m.setAttribute('content',escuro?'#0A2A5C':'#003478');}
aplicarTema(temaAtual);
const seletorTema=()=>`<div class="tema-sel" role="group" aria-label="Aparência do app">${TEMAS.map(([v,n])=>`<button type="button" data-act="tema" data-tema="${v}" aria-pressed="${temaAtual===v}">${n}</button>`).join('')}</div>`;
const SEAL=`<span class="brasoes"><img src="brasao-apmg.png" alt="Brasão da APMG"><img src="brasao-esfo.png" alt="Brasão da EsFO"></span>`;
const NOME='Almox EsFO',SUB='Cautela de materiais do almoxarifado';
const IC={
ini:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><path d="M3 11l9-7 9 7v9H3z"/><path d="M9 20v-6h6v6"/></svg>',
sol:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><path d="M4 7h16l-1.5 12h-13z"/><path d="M9 7a3 3 0 0 1 6 0"/></svg>',
rs:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><path d="M6 3h9l4 4v14H6zM9 12h7M9 16h7M9 8h3"/></svg>',
pf:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><circle cx="12" cy="8" r="4"/><path d="M4 21c1-4 4-6 8-6s7 2 8 6"/></svg>'
};

/* ============ Modal ============ */
const modal=$('#modal');
if(modal&&typeof modal.showModal!=='function'){
modal.showModal=function(){this.setAttribute('open','');this.style.cssText='display:block;position:fixed;inset:0;margin:auto;z-index:1000;max-height:92vh;max-width:640px;width:94vw;overflow:auto';};
modal.close=function(){this.removeAttribute('open');this.style.display='none';};
try{Object.defineProperty(modal,'open',{get(){return this.hasAttribute('open');}});}catch(e){}
}
function openModal(title,body,foot,sub){
modal.innerHTML=`<div class="mh"><div><h2>${title}</h2>${sub?`<p class="muted small">${sub}</p>`:''}</div><button class="x" data-act="fechar" aria-label="Fechar">×</button></div>
<div class="mb">${body}</div>${foot?`<div class="mf">${foot}</div>`:''}`;
if(!modal.open)modal.showModal();
}
const closeModal=()=>{if(modal.open)modal.close();assPend=null;};
modal.addEventListener('click',e=>{if(e.target===modal)closeModal();});
modal.addEventListener('close',()=>{if(fase==='app')render();});

/* ============ Ícones das categorias (desenho próprio, traço simples) ============ */
const CAT_IC={
uniforme:['Uniforme','<path d="M17 6l7 4 7-4 10 6-4 10-4-2v22H15V20l-4 2-4-10z"/><path d="M24 10v32"/><circle cx="27.5" cy="17" r="1.3" fill="currentColor"/><circle cx="27.5" cy="25" r="1.3" fill="currentColor"/><circle cx="27.5" cy="33" r="1.3" fill="currentColor"/>'],
cobertura:['Cobertura','<path d="M15 14h18l-2 20H17z"/><path d="M11 34q13 7 26 0"/><path d="M24 14V8"/><circle cx="24" cy="6" r="2.4"/><circle cx="24" cy="24" r="3.2"/>'],
luvas:['Luvas','<path d="M17 42V25q-3-4-5-6.5-1.6-2.6 1-3.3 2-.3 5 4.3V11a2 2 0 0 1 4 0v9V8a2 2 0 0 1 4 0v12V10a2 2 0 0 1 4 0v11-7a2 2 0 0 1 4 0v16q0 8-4 12z"/><path d="M17 36h14"/>'],
calcados:['Calçados','<path d="M6 32v-9q0-4 4-4h8q4 6 12 8l8 2q4 1 4 5v1H6z"/><path d="M6 38h36"/><path d="M19 23l4-2M22 26l4-2"/>'],
insignias:['Insígnias','<path d="M24 6l4.5 11 11.5.5-9 7.5 3 12-10-6.5-10 6.5 3-12-9-7.5 11.5-.5z"/>'],
correame:['Acessórios','<path d="M4 20h40v8H4z"/><path d="M18 15h12v18H18z"/><path d="M24 20v8"/>'],
espada:['Espada','<path d="M24 4v28"/><path d="M21 7l3-3 3 3"/><path d="M16 32h16"/><path d="M24 32v8"/><circle cx="24" cy="42" r="2"/>'],
generico:['Outros','<path d="M8 16l16-8 16 8v18l-16 8-16-8z"/><path d="M8 16l16 8 16-8M24 24v18"/>']
};
const icCat=c=>{if(c&&c.icone&&CAT_IC[c.icone])return c.icone;const n=norm(c&&c.nome);
return /unifor|fard|tunic|farda/.test(n)?'uniforme':/cobert|barret|quepe|bone/.test(n)?'cobertura':/luva/.test(n)?'luvas':/cal[cç]|sapat|bota|coturn/.test(n)?'calcados':
/insig|distint|plat/.test(n)?'insignias':/espad/.test(n)?'espada':/corre|acess|cinto/.test(n)?'correame':'generico';};
const svgCat=k=>`<svg viewBox="0 0 48 48" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${(CAT_IC[k]||CAT_IC.generico)[1]}</svg>`;

/* ============ Telas de entrada ============ */
const cab=sub=>`<div class="brand">${SEAL}<div><h1>${NOME}</h1><p class="nome-ext">${SUB}</p><p>${sub}</p></div></div>`;
function vNaoConfig(){return `<main class="login"><div class="login-card stack">${cab('Falta ligar o app ao Firebase')}<p>Preencha o arquivo <b>config.js</b> com os dados do projeto Firebase.</p></div></main>`;}
function vErro(){return `<main class="login"><div class="login-card stack">${cab('Não foi possível conectar')}<p class="erro">${esc(erroMsg)}</p><button class="btn btn-pri btn-block" data-act="recarregar">Tentar de novo</button></div></main>`;}
function vCarregando(){return `<div class="loading"><div><div class="spin"></div>Carregando…</div></div>`;}

/* ----- Campos de formulário ----- */
// Identificação: pedida no cadastro (como no SICAM)
function camposIdent(u,tipo){
u=u||{};
const grad=tipo==='oficial'
?`<label class="f"><span>Posto</span><select class="i" name="grad" required>${POSTOS.map(p=>`<option ${u.grad===p?'selected':''}>${p}</option>`).join('')}</select></label>`
:`<label class="f"><span>Graduação</span><input class="i" name="grad" value="${esc(u.grad||'Cad PM')}" required></label>`;
return `<div class="grid2">${grad}<label class="f"><span>Nome de guerra</span><input class="i" name="guerra" value="${esc(u.guerra||'')}" required></label></div>
<label class="f"><span>Nome completo</span><input class="i" name="nome" value="${esc(u.nome||'')}" required></label>`;
}
// Dados complementares: preenchidos pelo próprio militar dentro do sistema ("Meus dados")
function camposComp(u){
u=u||{};
return `<div class="grid2"><label class="f"><span>RG</span><input class="i" name="rg" value="${esc(u.rg||'')}" inputmode="numeric"></label>
<label class="f"><span>Telefone (WhatsApp)</span><input class="i" name="telefone" value="${esc(u.telefone||'')}" inputmode="tel" placeholder="(41) 9…"></label></div>
${u.tipo==='oficial'
?`<label class="f"><span>OPM / unidade</span><input class="i" name="opm" value="${esc(u.opm||'')}" placeholder="Ex.: 12º BPM"></label>`
:`<div class="grid2"><label class="f"><span>Ano do curso</span><select class="i" name="ano">${ANOS.map(([v,n])=>`<option value="${v}" ${String(u.ano||'1')===v?'selected':''}>${n}</option>`).join('')}</select></label>
<label class="f"><span>Pelotão</span><input class="i" name="pelotao" value="${esc(u.pelotao||'')}" placeholder="Ex.: 1º Pelotão Alfa"></label></div>
<label class="f"><span>Turma</span><input class="i" name="turma" value="${esc(u.turma||'')}" placeholder="Ex.: 1º CFO PM 2026"></label>`}`;
}
function camposRom(u){
u=u||{};
return `<div class="romaneio">${ROM.map(([k,n])=>`<label class="f"><span>${n}</span><input class="i" name="rom_${k}" value="${esc((u.romaneio||{})[k]||'')}" autocapitalize="characters"></label>`).join('')}</div>`;
}
// Tudo junto (edição pelo almoxarife)
const camposDados=u=>camposIdent(u,u.tipo)+camposComp(u)+`<h3 style="margin-top:1rem">Romaneio</h3>`+camposRom(u);
function lerDados(fd,tipo){
const g=k=>String(fd.get(k)||'').trim();const tem=k=>fd.has(k);
const o={};
if(tem('grad'))o.grad=g('grad');if(tem('guerra'))o.guerra=g('guerra').toUpperCase();if(tem('nome'))o.nome=g('nome');
if(tem('rg'))o.rg=g('rg');if(tem('telefone'))o.telefone=g('telefone');
if(tipo==='oficial'){if(tem('opm'))o.opm=g('opm');}else{if(tem('ano'))o.ano=g('ano');if(tem('pelotao'))o.pelotao=g('pelotao');if(tem('turma'))o.turma=g('turma');}
if(tem('rom_'+ROM[0][0])){o.romaneio={};ROM.forEach(([k])=>{const v=g('rom_'+k).toUpperCase();if(v)o.romaneio[k]=v;});}
return o;
}
/* Dados mínimos para pedir material: RG, pelotão (ou OPM) e romaneio */
const dadosCompletos=u=>!!(u&&u.rg&&(u.tipo==='oficial'?u.opm:u.pelotao)&&u.romaneio&&Object.keys(u.romaneio).length);

/* ----- Telas ----- */
const campoEmailSenha=almox=>`${almox?`<label class="f"><span>Usuário para entrar no sistema (ou e-mail institucional)</span><input class="i" name="email" type="text" required autocapitalize="off" placeholder="Ex.: almox"></label><p class="small muted" style="margin-top:-.4rem">Como a conta da Furrielação no SICAM: com um usuário (sem @) não é preciso confirmar e-mail, e o seu e-mail institucional fica livre para a sua conta de cadete.</p>`:`<label class="f"><span>E-mail institucional</span><input class="i" name="email" type="email" required autocapitalize="off" placeholder="nome@${esc(DOMINIOS[0])}"></label>`}
<div class="grid2"><label class="f"><span>Crie uma senha (mín. 8)</span><input class="i" name="senha" type="password" required minlength="8" autocomplete="new-password"></label>
<label class="f"><span>Repita a senha</span><input class="i" name="senha2" type="password" required minlength="8" autocomplete="new-password"></label></div>`;
function vSetup(){
return `<main class="login restrito"><div class="login-card">${cab('Configuração inicial')}
<form id="f-setup" class="stack" autocomplete="off" data-tipo="cadete" data-perfil="almox">
<p class="aviso">Esta tela só aparece uma vez. A conta criada aqui será a do <b>responsável pelo almoxarifado</b>, que depois libera os cadastros dos cadetes, dos oficiais e de outros auxiliares do almoxarifado.</p>
${camposIdent({},'cadete')}${campoEmailSenha(true)}
<label class="check"><input type="checkbox" name="seed" checked><span>Carregar o catálogo inicial do almoxarifado (fardamento, coberturas, luvas, calçados, insígnias e acessórios), com estoque zerado</span></label>
<p class="erro" id="setup-erro"></p>
<button class="btn btn-pri btn-block">Criar conta do almoxarifado</button>
</form></div></main>`;
}
function vLogin(){
const r=ui.tela==='almox';
return `<main class="login${r?' restrito':''}"><div class="login-card">${cab(r?'Painel do almoxarifado':'Almoxarifado · EsFO · APMG')}
${r?'<p style="margin:-.4rem 0 1rem"><span class="stamp c-stamp">Acesso restrito</span></p>':''}
<form id="f-login" class="stack" autocomplete="on">
<label class="f"><span>${r?'Usuário ou e-mail':'E-mail institucional'}</span><input class="i" name="email" type="${r?'text':'email'}" required autocapitalize="off" autocomplete="username" inputmode="email" placeholder="${r?'almox':'nome@'+esc(DOMINIOS[0])}"></label>
<label class="f"><span>Senha</span><input class="i" name="senha" type="password" required autocomplete="current-password"></label>
<p class="erro" id="login-erro">${esc(loginMsg)}</p>
<button class="btn btn-pri btn-block">${r?'Entrar no painel':'Entrar'}</button>
</form>
<div class="row between" style="margin-top:1rem"><button class="link" data-act="esqueci">Esqueci minha senha</button>
<button class="link" data-act="irCadastro" data-p="${r?'almox':'cadete'}">${r?'Solicitar conta do almoxarifado':'Criar minha conta'}</button></div>
<p class="acesso-f">${r?'<button class="link muted" data-act="tela" data-t="cadete">← Voltar ao acesso dos cadetes</button>':'<button class="link muted" data-act="tela" data-t="almox">Acesso restrito do almoxarifado</button>'}</p>
${r?'':`<div style="text-align:center">${seletorTema()}</div>`}<p class="versao-app">${NOME} v${VERSAO}</p>
</div></main>`;
}
function vCadastro(){
const almox=ui.cadPerfil==='almox';const t=almox?'cadete':ui.cadTipo;
return `<main class="login${almox?' restrito':''}"><div class="login-card">${cab(almox?'Solicitar conta do almoxarifado':'Criar minha conta')}
${almox?'<p class="aviso" style="margin-bottom:1rem">A conta do almoxarifado só funciona depois de aprovada pelo responsável pelo almoxarifado.</p>'
:`<div class="seg" role="group" style="margin-bottom:1rem"><button type="button" data-act="cadTipo" data-t="cadete" aria-pressed="${t==='cadete'}">Sou cadete da EsFO</button><button type="button" data-act="cadTipo" data-t="oficial" aria-pressed="${t==='oficial'}">Sou oficial</button></div>`}
<form id="f-cad" class="stack" autocomplete="off" data-tipo="${t}" data-perfil="${almox?'almox':'cadete'}">
${camposIdent({},t)}${campoEmailSenha(almox)}
<p class="small muted">A senha também serve para <b>assinar</b> as cautelas.${almox?'':' Depois de entrar, você completa seus dados e o romaneio em "Meus dados".'}</p>
<label class="check"><input type="checkbox" name="lgpd" required><span>Autorizo o uso dos meus dados pessoais exclusivamente para o controle de cautela de materiais do almoxarifado da EsFO (LGPD).</span></label>
<p class="small muted">Você vai receber um link no e-mail institucional para confirmar a conta. Depois, o almoxarifado libera seu acesso.</p>
<p class="erro" id="cad-erro"></p>
<button class="btn btn-pri btn-block">${almox?'Solicitar conta':'Criar conta'}</button>
<button type="button" class="btn btn-block" data-act="irLogin">Já tenho conta</button>
</form></div></main>`;
}
function vVerificar(){
const e=auth.currentUser?auth.currentUser.email:'';
return `<main class="login"><div class="login-card stack">${cab('Confirme seu e-mail')}
<p>Enviamos um link para <b>${esc(e)}</b>. Abra seu e-mail institucional, clique no link e volte aqui.</p>
<p class="aviso">Não chegou? Procure na caixa de spam ou lixo eletrônico. O remetente é noreply@${esc(FB.authDomain||'firebaseapp.com')}.</p>
<p class="erro" id="ver-erro"></p>
<button class="btn btn-pri btn-block" data-act="jaConfirmei">Já confirmei</button>
<button class="btn btn-block" data-act="reenviar">Reenviar o e-mail</button>
<button class="btn btn-block" data-act="sair">Sair</button><p class="versao-app">${NOME} v${VERSAO}</p></div></main>`;
}
function vAguardando(){
return `<main class="login"><div class="login-card stack">${cab('Cadastro recebido')}
<p>Seu e-mail foi confirmado. Agora o almoxarifado precisa liberar seu acesso.</p>
<p class="muted small">Esta tela atualiza sozinha assim que o acesso for liberado.</p>
<button class="btn btn-block" data-act="sair">Sair</button><p class="versao-app">${NOME} v${VERSAO}</p></div></main>`;
}

async function fazerLogin(fd){
const email=emailDe(fd.get('email'));
loginMsg='';ui.telaLogin=ui.tela;
try{await signInWithEmailAndPassword(auth,email,String(fd.get('senha')||''));}
catch(e){ui.telaLogin=null;$('#login-erro').textContent=erroFirebase(e);}
}
async function fazerCadastro(form,fd,setup){
const errEl=$(setup?'#setup-erro':'#cad-erro');const err=m=>{errEl.textContent=m;};
const perfilF=form.dataset.perfil||'cadete';
const email=perfilF==='almox'?emailDe(fd.get('email')):String(fd.get('email')||'').trim().toLowerCase();
if(!dominioOk(email)&&!(perfilF==='almox'&&ehFicticio(email)))return err(perfilF==='almox'?`Use um usuário sem @ (ex.: almox) ou o e-mail institucional (@${DOMINIOS[0]}).`:`Use seu e-mail institucional (@${DOMINIOS[0]}).`);
if(fd.get('senha')!==fd.get('senha2'))return err('As senhas não conferem.');
const tipo=form.dataset.tipo||'cadete',perfil=form.dataset.perfil||'cadete';
const dados=lerDados(fd,tipo);
if(!dados.guerra||!dados.nome)return err('Preencha o nome de guerra e o nome completo.');
const btn=form.querySelector('button.btn-pri');const rot=btn.textContent;btn.disabled=true;btn.textContent='Criando…';
bootstrapping=true;let cred=null;
try{
cred=await createUserWithEmailAndPassword(auth,email,String(fd.get('senha')));
const base={...dados,tipo,email,perfil,criadoEm:nowISO(),lgpd:nowISO(),romaneio:{}};
if(setup){
const b=writeBatch(db);
b.set(doc(db,'users',cred.user.uid),{...base,ativo:true,pendente:false});
b.set(doc(db,'config','setup'),{em:nowISO(),por:cred.user.uid,seed:!!fd.get('seed'),seeded:false});
await b.commit();
}else{
await setDoc(doc(db,'users',cred.user.uid),{...base,ativo:false,pendente:true});
}
if(!ehFicticio(email)){try{await sendEmailVerification(cred.user);}catch(e){console.warn(e);}}
bootstrapping=false;await aoMudarLogin(auth.currentUser);
}catch(e){
bootstrapping=false;console.error(e);
if(cred){try{await cred.user.delete();}catch(x){}}
err(erroFirebase(e));btn.disabled=false;btn.textContent=rot;
}
}

/* ============ App do cadete / oficial (celular) ============ */
function vApp(){
const u=me();const v=ui.view||'ini';
const n=acoesPendentes();
let corpo=v==='sol'?vSolicitar():v==='caut'?vMinhas():v==='pf'?vPerfil():vInicio();
const nav=[['ini','Início',IC.ini,n],['sol','Solicitar',IC.sol,0],['caut','Cautelas',IC.rs,0],['pf','Meus dados',IC.pf,0]];
return `<header class="m-top"><div class="wrap m-top-in"><img class="m-brasao" src="brasao-esfo.png" alt="Brasão da EsFO"><div><h1>${NOME}</h1><p>${esc(nomeU(u))}${turmaU(u)?' · '+esc(turmaU(u)):''}</p></div></div></header>
<main class="m-main">${corpo}</main>
${v==='sol'&&ui.cart.length?`<div class="cartbar"><div class="in"><span><b>${ui.cart.reduce((a,x)=>a+x.qtd,0)}</b> peça(s) no pedido</span><button class="btn" data-act="abrirPedido">Revisar e enviar</button></div></div>`:''}
<nav class="bnav"><div class="in">${nav.map(([k,l,ic,b])=>`<button data-act="go" data-v="${k}" ${v===k?'aria-current="page"':''}>${ic}<span>${l}${b?`<span class="dot-n">${b}</span>`:''}</span></button>`).join('')}</div></nav>`;
}
const minhas=()=>D.cautelas.filter(c=>c.userId===sess.userId);
function acoesPendentes(){
const assinar=minhas().filter(c=>c.status==='separada'&&!c.assinatura).length;
const trf=D.trfIn.filter(c=>c.transferPara===sess.userId&&c.transfer).length;
return assinar+trf;
}
function cardCautela(c,admin){
const u=user(c.userId);
return `<button class="card clickable${atrasada(c)?' card-late':''}" data-act="ver" data-id="${c.id}" style="margin-bottom:.6rem">
<div class="card-t"><div><span class="nr">${nr(c.num)}${c.origem==='balcao'?' · balcão':c.origem==='transferencia'?' · transferência':''}</span>
${admin?`<p style="font-weight:600">${esc(nomeU(u))} <span class="small muted">${esc(turmaU(u))}</span></p>`:''}
${itensLi(c,c.status==='cautelada')}</div>${stamp(c)}</div>
<dl class="meta">${c.status==='cautelada'||c.status==='separada'?`<dt>Devolver até</dt><dd>${c.prazo?fmtD(c.prazo):'sem prazo definido'}</dd>`:''}<dt>${c.status==='solicitada'?'Pedido em':'Atualizado'}</dt><dd>${fmt(c.atualizadoEm||c.criadoEm)}</dd></dl></button>`;
}
function vInicio(){
const u=me();let h='';
const assinar=minhas().filter(c=>c.status==='separada'&&!c.assinatura);
const aguard=minhas().filter(c=>c.status==='separada'&&c.assinatura);
const trf=D.trfIn.filter(c=>c.transferPara===sess.userId&&c.transfer);
const atras=minhas().filter(atrasada);
assinar.forEach(c=>{h+=`<div class="pend-box"><p><b>Material separado para você – ${nr(c.num)}</b></p>${itensLi(c)}<p class="small muted">Vá ao almoxarifado e assine com o material na sua frente.</p><div class="row" style="margin-top:.5rem"><button class="btn btn-pri" data-act="assinar" data-id="${c.id}">Assinar recebimento</button><button class="btn" data-act="ver" data-id="${c.id}">Detalhes</button></div></div>`;});
aguard.forEach(c=>{h+=`<div class="pend-box"><p><b>${nr(c.num)} assinada.</b> Aguarde o almoxarifado confirmar a entrega.</p></div>`;});
trf.forEach(c=>{h+=`<div class="pend-box"><p><b>Transferência para você</b> – ${esc(nomeM(c.userId))} quer transferir:</p><ul class="itens">${(c.transfer.itens||[]).map(x=>{const l=c.itens[x.i]||{};return `<li><b>${x.qtd}×</b><span>${esc(l.nome)}${tamTxt(l.tam)?` <span class="tag">${esc(l.tam)}</span>`:''}</span></li>`;}).join('')}</ul>
<div class="row" style="margin-top:.5rem"><button class="btn btn-pri" data-act="aceitarTrf" data-id="${c.id}">Aceitar e assinar</button><button class="btn btn-warn" data-act="recusarTrf" data-id="${c.id}">Recusar</button></div></div>`;});
atras.forEach(c=>{h+=`<div class="pend-box red"><p><b>${nr(c.num)} em atraso</b> – o prazo de devolução era ${fmtD(c.prazo)}. Procure o almoxarifado.</p></div>`;});
const ativas=minhas().filter(c=>c.status==='cautelada');
const andamento=minhas().filter(c=>c.status==='solicitada'||c.status==='separada');
// material em nome do militar (soma de todas as cautelas)
const soma={};ativas.forEach(c=>(c.itens||[]).forEach(l=>{const q=pend(l);if(!q)return;const k=l.nome+'|'+(l.tam||'');soma[k]=soma[k]||{nome:l.nome,tam:l.tam,qtd:0};soma[k].qtd+=q;}));
const linhas=Object.values(soma).sort((a,b)=>a.nome.localeCompare(b.nome,'pt-BR'));
h+=`<div class="sec-h"><h2>Material em seu nome</h2><span class="muted small">${linhas.reduce((a,x)=>a+x.qtd,0)} peça(s)</span></div>`;
h+=linhas.length?`<div class="card"><ul class="itens">${linhas.map(l=>`<li><b>${l.qtd}×</b><span>${esc(l.nome)}${tamTxt(l.tam)?` <span class="tag">${esc(l.tam)}</span>`:''}</span></li>`).join('')}</ul></div>`
:`<div class="empty">Nenhum material cautelado em seu nome.<br><button class="btn btn-pri" style="margin-top:.7rem" data-act="go" data-v="sol">Solicitar material</button></div>`;
if(andamento.length)h+=`<div class="sec-h"><h2>Pedidos em andamento</h2></div>`+andamento.map(c=>cardCautela(c)).join('');
if(ativas.length)h+=`<div class="sec-h"><h2>Cautelas ativas</h2></div>`+ativas.map(c=>cardCautela(c)).join('');
if(!dadosCompletos(u))h=boxCompletar()+h;
return h;
}
const boxCompletar=()=>`<div class="aviso" style="margin-bottom:.8rem">Atualize seus dados e o <b>romaneio</b> quando puder: com as suas medidas o sistema já sugere o tamanho certo de cada peça. <button class="link" data-act="go" data-v="pf">Atualizar agora</button></div>`;
function vSolicitar(){
const u=me();
const cats=D.cats.filter(c=>D.itens.some(i=>i.catId===c.id&&i.ativo!==false));
if(ui.cat&&!cats.some(c=>c.id===ui.cat))ui.cat=null;
if(!ui.cat){
if(!cats.length)return `<div class="empty">Nenhum material cadastrado ainda.</div>`;
return `<div class="sec-h"><h2>O que você precisa?</h2></div><div class="cat-grid2">${cats.map(c=>{const n=D.itens.filter(i=>i.catId===c.id&&i.ativo!==false).length;
return `<button class="cat-tile" data-act="catSol" data-id="${c.id}"><span class="cat-ic">${svgCat(icCat(c))}</span><h3>${esc(c.nome)}</h3><span class="n">${n} ${n===1?'item':'itens'}</span></button>`;}).join('')}</div>`;}
const c=cats.find(x=>x.id===ui.cat);
let h=`<button class="voltar" data-act="catSol" data-id="">← Categorias</button><div class="cat-topo"><span class="cat-ic">${svgCat(icCat(c))}</span><h2>${esc(c.nome)}</h2></div>`;
const its=D.itens.filter(i=>i.catId===ui.cat&&i.ativo!==false);
h+=its.map(it=>{
const sug=sugTam(it,u);const sel=(ui.tamSel||{})[it.id]||sug||(it.tamanhos||[])[0];
const unico=(it.tamanhos||[]).length<=1;
const noCart=ui.cart.filter(x=>x.itemId===it.id).reduce((a,x)=>a+x.qtd,0);
return `<div class="card" style="margin-bottom:.6rem"><div class="eq"><div><h3>${esc(it.nome)}</h3>
<p class="avail">${it.consumo?'Entrega definitiva (não precisa devolver)':'Cautela com devolução'} · ${esc((UNID[it.unidade]||UNID.un)[0])}${it.campo&&!sug?` · <button class="link" data-act="go" data-v="pf">informe seu tamanho no romaneio</button>`:''}</p></div>
<button class="btn btn-pri btn-sm" data-act="addCart" data-id="${it.id}">Adicionar</button></div>
${unico?'':`<div class="tam-sel" role="group" aria-label="Tamanho">${(it.tamanhos||[]).map(t=>{const d=est(it,t).disp;return `<button type="button" data-act="tam" data-id="${it.id}" data-t="${esc(t)}" aria-pressed="${t===sel}" class="${t===sug?'sug':''}" title="${d>0?'Disponível':'Sem estoque no momento'}">${esc(t)}${d>0?'':'<span class="se" aria-label="sem estoque">•</span>'}</button>`;}).join('')}</div>${sug?`<p class="small muted" style="margin-top:.3rem">Sublinhado em dourado: seu tamanho pelo romaneio (${esc(sug)}).</p>`:''}`}
${est(it,sel).disp<=0?`<p class="small c-brass" style="margin-top:.3rem">${unico?'Sem estoque no momento':'Tamanho '+esc(sel)+' sem estoque no momento'}: você pode pedir mesmo assim, e o almoxarifado avisa quando separar.</p>`:''}
${noCart?`<p class="small c-ok" style="margin-top:.3rem">${noCart} no pedido</p>`:''}</div>`;}).join('');
return h;
}
function addCart(id){
const it=item(id);const t=(ui.tamSel||{})[id]||sugTam(it,me())||(it.tamanhos||[])[0]||'Único';
const x=ui.cart.find(c=>c.itemId===id&&c.tam===t);
if(x){if(x.qtd>=5){toast('Máximo de 5 por item.',true);return;}x.qtd++;}else ui.cart.push({itemId:id,tam:t,qtd:1});
toast(`${it.nome}${tamTxt(t)?' ('+t+')':''} adicionado.`);render();
}
function abrirPedido(){
if(!ui.cart.length)return;
openModal('Revisar pedido',`<form id="f-pedido" class="stack">
<div class="card">${ui.cart.map((x,i)=>{const it=item(x.itemId);return `<div class="cart-li"><span class="nm">${esc(it.nome)}${tamTxt(x.tam)?` <span class="tag">${esc(x.tam)}</span>`:''}</span>
<button type="button" class="mini" data-act="cartQ" data-i="${i}" data-d="-1">−</button><b>${x.qtd}</b><button type="button" class="mini" data-act="cartQ" data-i="${i}" data-d="1">+</button><button type="button" class="mini rm" data-act="cartRm" data-i="${i}">×</button></div>`;}).join('')}</div>
<label class="f"><span>Observação (opcional)</span><textarea class="i" name="obs" placeholder="Ex.: para o desfile de 7 de Setembro"></textarea></label>
<p class="small muted">O almoxarifado separa o material e avisa aqui no app. Você assina o recebimento quando for retirar.</p>
<p class="erro" id="ped-erro"></p></form>`,
`<button class="btn" data-act="limparCart">Limpar</button><button class="btn btn-pri" data-act="enviarPedido">Enviar pedido</button>`);
}
async function proxNumero(tx){
const ref=doc(db,'config','contador');const s=await tx.get(ref);
const n=s.exists()?(s.data().n||0)+1:1;
if(s.exists())tx.update(ref,{n});else tx.set(ref,{n});
return n;
}
async function enviarPedido(){
if(!ui.cart.length)return;
const obs=String(($('#f-pedido [name=obs]')||{}).value||'').trim();
const itens=ui.cart.map(x=>{const it=item(x.itemId);return {itemId:x.itemId,nome:it.nome,tam:x.tam,qtd:x.qtd,dev:0,trf:0,consumo:!!it.consumo,unidade:it.unidade||'un'};});
try{
await runTransaction(db,async tx=>{const num=await proxNumero(tx);const ref=doc(collection(db,'cautelas'));
tx.set(ref,{num,userId:sess.userId,origem:'app',status:'solicitada',itens,obs,prazo:null,assinatura:null,transferPara:null,transfer:null,
criadoEm:nowISO(),atualizadoEm:nowISO(),log:[entrada('Solicitada',obs)]});});
ui.cart=[];closeModal();ui.view='ini';render();toast('Pedido enviado ao almoxarifado.');
pedirNotificacao();
}catch(e){console.error(e);const el=$('#ped-erro');if(el)el.textContent=erroFirebase(e);}
}
function pedirNotificacao(){try{if('Notification' in window&&Notification.permission==='default')Notification.requestPermission();}catch(e){}}
function vMinhas(){
const l=minhas().slice().sort((a,b)=>String(b.criadoEm).localeCompare(String(a.criadoEm)));
return `<div class="sec-h"><h2>Minhas cautelas</h2><span class="muted small">${l.length}</span></div>`+(l.length?l.map(c=>cardCautela(c)).join(''):'<div class="empty">Nenhuma cautela ainda.</div>');
}
function vPerfil(){
const u=me();const bio=temBioAqui();
return `<div class="sec-h"><h2>Meus dados</h2></div>
<p class="small muted" style="margin-bottom:.6rem">Preencha ou atualize quando quiser. Nada aqui é obrigatório para fazer pedidos, mas o romaneio ajuda o almoxarifado a separar o tamanho certo.</p>
<div class="card stack"><dl class="dados-mil"><dt>Militar</dt><dd>${esc(nomeU(u))}</dd><dt>Nome</dt><dd>${esc(u.nome)}</dd><dt>E-mail</dt><dd>${esc(u.email)}</dd></dl>
<p class="small muted">Para corrigir nome, graduação ou e-mail, procure o almoxarifado.</p></div>
<form id="f-perfil" class="stack" style="margin-top:.8rem">
<div class="card stack"><h3>Dados complementares</h3>${camposComp(u)}</div>
<div class="card stack"><h3>Romaneio</h3><p class="small muted">Suas medidas. Use o número ou o tamanho que está na etiqueta da peça que você veste (ex.: 41, M, 56).</p>${camposRom(u)}</div>
<p class="erro" id="pf-erro"></p><button class="btn btn-pri btn-block">Salvar meus dados</button></form>
<div class="card stack" style="margin-top:.8rem"><h3>Assinatura</h3>
${bio?'<p class="pill ok">Digital / Face ID ativados neste aparelho</p>':bioOk?`<p class="small">Ative para assinar as cautelas com digital, Face ID ou a senha do celular.</p><button class="btn btn-pri" data-act="ativarBio">Ativar digital / Face ID neste aparelho</button>`:'<p class="small muted">Este aparelho não oferece digital/Face ID para sites. Assine com a senha.</p>'}
<button class="btn" data-act="senha">Trocar minha senha</button></div>
<div class="card stack" style="margin-top:.8rem"><h3>Aparência</h3>${seletorTema()}</div>
<button class="btn btn-warn btn-block" style="margin-top:1rem" data-act="sair">Sair</button><p class="versao-app">${NOME} v${VERSAO}</p>`;
}
async function salvarPerfil(fd){
const u=me();const d=lerDados(fd,u.tipo);
const up={rg:d.rg||'',telefone:d.telefone||'',romaneio:d.romaneio||{},atualizadoEm:nowISO()};
if(u.tipo==='oficial')up.opm=d.opm||'';else{up.pelotao=d.pelotao||'';up.ano=d.ano||'';up.turma=d.turma||'';}
try{await updateDoc(doc(db,'users',u.id),up);toast('Dados salvos.');window.scrollTo(0,0);}
catch(e){$('#pf-erro').textContent=erroFirebase(e);}
}
function trocarSenha(){
openModal('Trocar senha',`<form id="f-senha" class="stack"><label class="f"><span>Senha atual</span><input class="i" type="password" name="a" required autocomplete="current-password"></label>
<label class="f"><span>Nova senha (mín. 8)</span><input class="i" type="password" name="n" required minlength="8" autocomplete="new-password"></label>
<p class="erro" id="senha-erro"></p><button class="btn btn-pri btn-block">Trocar senha</button></form>`);
}
async function salvarSenha(fd){
const a=auth.currentUser;
try{await reauthenticateWithCredential(a,EmailAuthProvider.credential(a.email,String(fd.get('a'))));await updatePassword(a,String(fd.get('n')));closeModal();toast('Senha alterada.');}
catch(e){$('#senha-erro').textContent=(e.code==='auth/invalid-credential'||e.code==='auth/wrong-password')?'Senha atual incorreta.':erroFirebase(e);}
}

/* ============ Detalhe de uma cautela ============ */
function verCautela(id){
const c=C(id);if(!c)return;const u=user(c.userId);const adm=ehAlmox();const meu=c.userId===sess.userId;
const a=c.assinatura;
let acoes='';
if(adm){
if(c.status==='solicitada')acoes+=`<button class="btn btn-warn" data-act="recusar" data-id="${c.id}">Recusar</button><button class="btn btn-pri" data-act="separar" data-id="${c.id}">Separar material</button>`;
if(c.status==='separada'){acoes+=`<button class="btn btn-warn" data-act="cancelarSep" data-id="${c.id}">Cancelar e devolver ao estoque</button>`;
acoes+=a?`<button class="btn btn-pri" data-act="entregar" data-id="${c.id}">Confirmar entrega</button>`:`<button class="btn btn-pri" data-act="assBalcao" data-id="${c.id}">Assinar no balcão (senha do militar)</button>`;}
if(c.status==='cautelada'&&pendentes(c).length)acoes+=`<button class="btn" data-act="prazo" data-id="${c.id}">Prazo</button><button class="btn btn-pri" data-act="devolver" data-id="${c.id}">Registrar devolução</button>`;
}else if(meu){
if(c.status==='solicitada')acoes+=`<button class="btn btn-warn" data-act="cancelarPedido" data-id="${c.id}">Cancelar pedido</button>`;
if(c.status==='separada'&&!a)acoes+=`<button class="btn btn-pri" data-act="assinar" data-id="${c.id}">Assinar recebimento</button>`;
if(c.status==='cautelada'&&pendentes(c).length)acoes+=c.transferPara?`<button class="btn btn-warn" data-act="desistirTrf" data-id="${c.id}">Desistir da transferência</button>`:`<button class="btn btn-pri" data-act="transferir" data-id="${c.id}">Transferir para outro militar</button>`;
}
if(c.assinatura)acoes=`<button class="btn" data-act="termo" data-id="${c.id}">Termo de cautela (PDF)</button>`+acoes;
openModal(`Cautela ${nr(c.num)}`,`<div class="ficha">${stamp(c,true)}<p style="font-weight:600">${esc(nomeU(u))}</p><p class="small muted">${esc(turmaU(u))}</p>
${itensLi(c)}
<dl class="meta"><dt>Origem</dt><dd>${c.origem==='balcao'?'Cautela no balcão':c.origem==='transferencia'?`Transferência de ${esc(nomeM(c.deUser))} (${nr(c.deNum)})`:'Pedido pelo app'}</dd>
${c.status!=='solicitada'?`<dt>Devolver até</dt><dd>${c.prazo?fmtD(c.prazo):'sem prazo definido'}</dd>`:''}
${a?`<dt>Assinatura</dt><dd>${fmt(a.em)}, ${esc(FORMA[a.metodo]||a.metodo)}</dd>`:''}
${c.obs?`<dt>Obs.</dt><dd>${esc(c.obs)}</dd>`:''}
${c.transferPara?`<dt>Transferência</dt><dd>oferecida a ${esc(nomeM(c.transferPara))}, aguardando aceite</dd>`:''}</dl></div>
${(c.ocorrencias||[]).length?`<div class="sec-h"><h3>Ocorrências na devolução</h3></div><ul class="feed">${c.ocorrencias.map(o=>`<li>${o.qtd}× ${esc(o.nome)}${tamTxt(o.tam)?' ('+esc(o.tam)+')':''} – <b class="c-stamp">${esc(o.estado)}</b>${o.obs?' – '+esc(o.obs):''}<time>${fmt(o.t)}</time></li>`).join('')}</ul>`:''}
<div class="sec-h"><h3>Histórico</h3></div><ul class="feed">${(c.log||[]).slice().reverse().map(x=>`<li><b>${esc(x.a)}</b> – ${esc(nomeM(x.por))}${x.obs?`<br><span class="small">${esc(x.obs)}</span>`:''}<time>${fmt(x.t)}</time></li>`).join('')}</ul>`,acoes);
}
async function cancelarPedido(id){
const c=C(id);if(!c||c.status!=='solicitada')return;
try{await updateDoc(doc(db,'cautelas',id),{status:'cancelada',log:[...(c.log||[]),entrada('Cancelada pelo militar')]});closeModal();toast('Pedido cancelado.');}
catch(e){toast(erroFirebase(e),true);}
}

/* ============ Assinatura: senha do Almox EsFO, ou digital / Face ID / senha do celular ============ */
let assPend=null,bioRecente=null;
const temBioAqui=()=>{const u=me();const id=u&&bioLocal(u.id);return !!(bioOk&&id&&((u.passkeys||[]).some(k=>k.id===id)||bioRecente===id));};
const FORMA={senha:'com a senha do Almox EsFO, no celular do militar',biometria:'com digital, Face ID ou senha do celular do militar',balcao:'com a senha do militar, no aparelho do almoxarifado'};
function textoAssinatura(c,em,acao){
return `ALMOX ESFO | ${acao} | Cautela ${nr(c.num)} | ${nomeM(sess.userId)} | Material: ${itensTxt(c)} | Prazo: ${c.prazo?fmtD(c.prazo):'sem prazo'} | ${em}`;
}
function blocoAssinatura(rot){
const bio=temBioAqui();
return `<div class="ass-box">
${bio?`<button type="button" class="btn btn-pri btn-block" data-act="assBio">👆 ${rot} com digital ou Face ID</button><p class="ou">ou</p>`:''}
<form id="f-ass" class="stack" autocomplete="off">
<label class="f"><span>${bio?'Senha do Almox EsFO':'Sua senha do Almox EsFO'}</span><input class="i" type="password" name="s" required autocomplete="current-password"></label>
<p class="erro" id="ass-erro"></p>
<button class="btn ${bio?'':'btn-pri '}btn-block">${rot} com senha</button></form>
${bioOk&&!bio?`<p class="small muted" style="margin-top:.6rem">Quer assinar com digital ou Face ID? <button type="button" class="link" data-act="ativarBioAqui">Ative neste aparelho</button> (só uma vez).</p>`:''}
</div>`;
}
function pedirAssinatura(o){assPend=o;openModal(o.titulo,o.corpo+blocoAssinatura(o.rotulo||'Assinar'),'',o.sub||'');assPend=o;}
async function hashTexto(t){return b64u(await crypto.subtle.digest('SHA-256',new TextEncoder().encode(t)));}
async function concluirAssinatura(ass){
const p=assPend;if(!p)return;
try{await p.onOk(ass);}catch(e){console.error(e);const el=$('#ass-erro');if(el)el.textContent=erroFirebase(e);}
}
async function assinarComSenha(fd){
const a=auth.currentUser,err=m=>{const el=$('#ass-erro');if(el)el.textContent=m;};
try{await reauthenticateWithCredential(a,EmailAuthProvider.credential(a.email,String(fd.get('s'))));}
catch(e){err((e.code==='auth/invalid-credential'||e.code==='auth/wrong-password')?'Senha incorreta.':erroFirebase(e));return;}
const em=nowISO(),dados=assPend.dados(em);
await concluirAssinatura({por:sess.userId,em,metodo:'senha',dados,hash:await hashTexto(dados),aparelho:navigator.userAgent.slice(0,160)});
}
async function assinarComBio(){
const credId=bioLocal(sess.userId);if(!assPend||!credId)return;
const em=nowISO(),dados=assPend.dados(em),h=await crypto.subtle.digest('SHA-256',new TextEncoder().encode(dados));
let a;
try{a=await navigator.credentials.get({publicKey:{challenge:h,rpId:location.hostname,allowCredentials:[{type:'public-key',id:ub64u(credId)}],userVerification:'required',timeout:60000}});}
catch(e){const el=$('#ass-erro');if(el)el.textContent='A digital ou o Face ID não foram confirmados. Tente de novo ou use a senha.';return;}
await concluirAssinatura({por:sess.userId,em,metodo:'biometria',dados,hash:b64u(h),credId:a.id,
authData:b64u(a.response.authenticatorData),clientData:b64u(a.response.clientDataJSON),sig:b64u(a.response.signature),aparelho:navigator.userAgent.slice(0,160)});
}
async function ativarBio(){
const u=me();let c;
try{c=await navigator.credentials.create({publicKey:{challenge:crypto.getRandomValues(new Uint8Array(32)),rp:{name:NOME,id:location.hostname},
user:{id:new TextEncoder().encode(u.id),name:u.email,displayName:nomeU(u)},pubKeyCredParams:[{type:'public-key',alg:-7},{type:'public-key',alg:-257}],
authenticatorSelection:{authenticatorAttachment:'platform',userVerification:'required',residentKey:'preferred'},timeout:60000,attestation:'none'}});}
catch(e){toast('Não foi possível ativar. Confira se o celular tem digital ou Face ID cadastrados.',true);return;}
let pk=null,alg=null;try{pk=c.response.getPublicKey?b64u(c.response.getPublicKey()):null;alg=c.response.getPublicKeyAlgorithm?c.response.getPublicKeyAlgorithm():null;}catch(e){}
const lista=[...(u.passkeys||[]),{id:c.id,publicKey:pk,alg,criadoEm:nowISO(),aparelho:navigator.userAgent.slice(0,160)}].slice(-5);
await updateDoc(doc(db,'users',u.id),{passkeys:lista});
try{localStorage.setItem(bioKey(u.id),c.id);}catch(e){}
bioRecente=c.id;toast('Assinatura por digital / Face ID ativada neste aparelho.');render();
}
function assinar(id){
const c=C(id);if(!c||c.status!=='separada'||c.assinatura)return;
pedirAssinatura({titulo:'Assinar recebimento – '+nr(c.num),sub:'Assine só com o material na sua frente.',rotulo:'Assinar',
corpo:`<div class="ficha"><p style="font-weight:600">${esc(nomeM(c.userId))}</p>${itensLi(c)}<dl class="meta"><dt>Devolver até</dt><dd>${c.prazo?fmtD(c.prazo):'sem prazo definido'}</dd></dl></div>
<p class="aviso">Declaro que recebi o material acima do almoxarifado da EsFO, conferi tamanhos, quantidades e estado de conservação, e me responsabilizo pela guarda e pela devolução${c.prazo?' até '+fmtD(c.prazo):' quando solicitado'}.</p>`,
dados:em=>textoAssinatura(c,em,'Recebimento'),
onOk:async ass=>{const cc=C(id);if(!cc||cc.status!=='separada'||cc.assinatura)throw {msg:'Esta cautela já foi assinada ou mudou de situação.'};
await updateDoc(doc(db,'cautelas',id),{assinatura:ass,log:[...(cc.log||[]),{t:ass.em,a:'Assinada',por:sess.userId,obs:FORMA[ass.metodo]||ass.metodo}]});
closeModal();toast('Recebimento assinado. O almoxarifado vai confirmar a entrega.');}});
}

/* ============ Transferência de cautela entre militares ============ */
function transferir(id){
const c=C(id);if(!c||c.status!=='cautelada'||c.transferPara)return;
const lista=D.dir.filter(u=>u.id!==sess.userId);
const linhas=(c.itens||[]).map((l,i)=>({l,i})).filter(x=>pend(x.l)>0);
openModal('Transferir material – '+nr(c.num),`<form id="f-trf" data-id="${c.id}" class="stack">
<label class="f"><span>Para quem?</span><input class="i" data-inp="trfq" id="trf-q" placeholder="Digite o nome de guerra ou o pelotão" autocomplete="off"></label>
<div class="dir-lista" id="trf-dir">${lista.map(u=>`<label data-busca="${esc(norm(nomeU(u)+' '+(u.nome||'')+' '+turmaU(u)))}"><input type="radio" name="para" value="${u.id}" required><span>${esc(nomeU(u))} <span class="small muted">${esc(turmaU(u))}</span></span></label>`).join('')||'<p class="muted small" style="padding:.6rem">Nenhum militar disponível.</p>'}</div>
<div><span class="sep-lbl">O que transferir</span><ul class="trf-lista">${linhas.map(({l,i})=>`<li><span class="nm">${esc(l.nome)}${tamTxt(l.tam)?` <span class="tag">${esc(l.tam)}</span>`:''}</span><input class="i q" type="number" min="0" max="${pend(l)}" value="${pend(l)}" name="q${i}" data-i="${i}"><span class="small muted">de ${pend(l)}</span></li>`).join('')}</ul></div>
<p class="small muted">O outro militar precisa aceitar e assinar no celular dele. Até lá, o material continua em seu nome.</p>
<p class="erro" id="trf-erro"></p><button class="btn btn-pri btn-block">Continuar para assinatura</button></form>`);
}
function filtrarTrf(v){const q=norm(v);$$('#trf-dir label').forEach(l=>{l.hidden=!!q&&!l.dataset.busca.includes(q);});}
function confirmarTransf(form,fd){
const c=C(form.dataset.id);if(!c)return;
const para=String(fd.get('para')||'');if(!para){$('#trf-erro').textContent='Escolha o militar que vai receber.';return;}
const itens=$$('#f-trf input.q').map(x=>({i:+x.dataset.i,qtd:Math.min(int(x.value),pend(c.itens[+x.dataset.i]))})).filter(x=>x.qtd>0);
if(!itens.length){$('#trf-erro').textContent='Escolha pelo menos uma peça.';return;}
const d=D.dir.find(u=>u.id===para)||{};
const txt=itens.map(x=>{const l=c.itens[x.i];return `${x.qtd}× ${l.nome}${tamTxt(l.tam)?' ('+l.tam+')':''}`;}).join(', ');
pedirAssinatura({titulo:'Assinar transferência',rotulo:'Assinar',corpo:`<div class="ficha"><p>De <b>${esc(nomeM(c.userId))}</b> para <b>${esc(nomeU(d))}</b></p><p>${esc(txt)}</p></div>
<p class="aviso">Declaro que entreguei o material acima a ${esc(nomeU(d))}. A responsabilidade só passa para ele(a) depois do aceite.</p>`,
dados:em=>`ALMOX ESFO | Transferência | Cautela ${nr(c.num)} | De ${nomeM(c.userId)} para ${nomeU(d)} | ${txt} | ${em}`,
onOk:async ass=>{const cc=C(c.id);if(!cc||cc.status!=='cautelada'||cc.transferPara)throw {msg:'Esta cautela mudou de situação.'};
await updateDoc(doc(db,'cautelas',c.id),{transferPara:para,transfer:{para,itens,em:ass.em,assinatura:ass},log:[...(cc.log||[]),{t:ass.em,a:'Transferência oferecida',por:sess.userId,obs:`Para ${nomeU(d)}: ${txt}`}]});
closeModal();toast('Transferência enviada. Aguarde o aceite.');}});
}
async function desistirTrf(id){
const c=C(id);if(!c||!c.transferPara)return;
try{await updateDoc(doc(db,'cautelas',id),{transferPara:null,transfer:null,log:[...(c.log||[]),entrada('Transferência cancelada')]});closeModal();toast('Transferência cancelada.');}
catch(e){toast(erroFirebase(e),true);}
}
function aceitarTrf(id){
const c=C(id);if(!c||!c.transfer)return;
const t=c.transfer;const txt=t.itens.map(x=>{const l=c.itens[x.i];return `${x.qtd}× ${l.nome}${tamTxt(l.tam)?' ('+l.tam+')':''}`;}).join(', ');
pedirAssinatura({titulo:'Aceitar transferência',rotulo:'Aceitar',corpo:`<div class="ficha"><p>De <b>${esc(nomeM(c.userId))}</b> (${nr(c.num)})</p><p>${esc(txt)}</p><dl class="meta"><dt>Devolver até</dt><dd>${c.prazo?fmtD(c.prazo):'sem prazo definido'}</dd></dl></div>
<p class="aviso">Declaro que recebi o material acima e assumo a responsabilidade pela guarda e pela devolução ao almoxarifado da EsFO.</p>`,
dados:em=>`ALMOX ESFO | Aceite de transferência | Cautela ${nr(c.num)} | De ${nomeM(c.userId)} para ${nomeM(sess.userId)} | ${txt} | ${em}`,
onOk:async ass=>{
await runTransaction(db,async tx=>{
const ref=doc(db,'cautelas',id);const s=await tx.get(ref);const o=s.data();
if(!o||o.transferPara!==sess.userId||!o.transfer||o.status!=='cautelada')throw {msg:'Esta transferência foi cancelada ou já foi concluída.'};
const num=await proxNumero(tx);
const itens=o.itens.map(l=>({...l}));const novos=[];
o.transfer.itens.forEach(x=>{const l=itens[x.i];const q=Math.min(x.qtd,pend(l));if(q<=0)return;l.trf=(l.trf||0)+q;novos.push({itemId:l.itemId,nome:l.nome,tam:l.tam,qtd:q,dev:0,trf:0,consumo:false,unidade:l.unidade||'un'});});
if(!novos.length)throw {msg:'Não há mais material para transferir nesta cautela.'};
const nref=doc(collection(db,'cautelas'));
tx.set(nref,{num,userId:sess.userId,origem:'transferencia',deCautela:id,deUser:o.userId,deNum:o.num,status:'cautelada',itens:novos,obs:'',prazo:o.prazo||null,
assinatura:ass,transferPara:null,transfer:null,criadoEm:nowISO(),atualizadoEm:nowISO(),entregueEm:ass.em,
log:[{t:o.transfer.em,a:'Transferência assinada por quem entregou',por:o.userId,obs:''},{t:ass.em,a:'Recebida por transferência',por:sess.userId,obs:`De ${nomeM(o.userId)} – ${nr(o.num)}`}]});
const resta=itens.some(l=>pend(l)>0);
tx.update(ref,{itens,transferPara:null,transfer:null,status:resta?'cautelada':'transferida',log:[...(o.log||[]),{t:ass.em,a:'Transferência aceita',por:sess.userId,obs:`Nova cautela ${nr(num)}`}]});
});
closeModal();toast('Transferência aceita. O material agora está em seu nome.');}});
}
async function recusarTrf(id){
const c=C(id);if(!c)return;
try{await updateDoc(doc(db,'cautelas',id),{transferPara:null,transfer:null,log:[...(c.log||[]),entrada('Transferência recusada')]});toast('Transferência recusada.');}
catch(e){toast(erroFirebase(e),true);}
}

/* ============ Painel do almoxarifado ============ */
const ativasA=()=>D.cautelas.filter(c=>c.status==='cautelada');
const solicitadas=()=>D.cautelas.filter(c=>c.status==='solicitada').sort((a,b)=>String(a.criadoEm).localeCompare(String(b.criadoEm)));
const separadas=()=>D.cautelas.filter(c=>c.status==='separada').sort((a,b)=>String(a.atualizadoEm).localeCompare(String(b.atualizadoEm)));
const pendCad=()=>D.users.filter(u=>u.pendente);
const cauteladoDe=(itemId,tam)=>ativasA().reduce((a,c)=>a+(c.itens||[]).filter(l=>l.itemId===itemId&&l.tam===tam).reduce((b,l)=>b+pend(l),0),0);
const separadoDe=(itemId,tam)=>separadas().reduce((a,c)=>a+(c.itens||[]).filter(l=>l.itemId===itemId&&l.tam===tam).reduce((b,l)=>b+l.qtd,0),0);
function vAdmin(){
const v=ui.view||'painel';const u=me();
const nav=[['painel','Painel',0],['pedidos','Pedidos',solicitadas().length+separadas().filter(c=>c.assinatura).length],['uso','Em uso',ativasA().filter(atrasada).length],
['material','Material',0],['militares','Militares',pendCad().length],['hist','Histórico',0],['rel','Relatórios',0]];
const corpo=v==='pedidos'?vPedidos():v==='uso'?vEmUso():v==='material'?vMaterial():v==='militares'?vMilitares():v==='hist'?vHist():v==='rel'?vRelatorios():vPainel();
return `<div class="shell"><aside class="side"><div class="brand"><img class="seal-img" src="brasao-esfo.png" alt="Brasão da EsFO"><div><h1>${NOME}</h1><p>Almoxarifado</p></div></div>
${nav.map(([k,l,b])=>`<button class="nav-b" data-act="go" data-v="${k}" ${v===k?'aria-current="page"':''}><span>${l}</span>${b?`<span class="badge${k==='uso'?' red':''}">${b}</span>`:''}</button>`).join('')}
<button class="nav-b" data-act="balcao"><span>+ Cautela no balcão</span></button>
<div class="foot"><div class="who">${esc(nomeU(u))}</div>${seletorTema()}<button class="nav-b" data-act="senha">Trocar senha</button><button class="nav-b" data-act="sair">Sair</button></div></aside>
<main class="a-main">${corpo}</main></div>`;
}
function vPainel(){
const sol=solicitadas(),sep=separadas(),uso=ativasA(),atr=uso.filter(atrasada),pc=pendCad();
const pecas=uso.reduce((a,c)=>a+(c.itens||[]).reduce((b,l)=>b+pend(l),0),0);
let h=`<div class="a-head"><div><h1>Painel</h1><p>${new Date().toLocaleDateString('pt-BR',{weekday:'long',day:'2-digit',month:'long'})}</p></div><button class="btn btn-pri" data-act="balcao">+ Cautela no balcão</button></div>
<div class="kpis"><button class="kpi" data-act="go" data-v="pedidos"><strong>${sol.length}</strong><span>Pedidos novos</span></button>
<button class="kpi" data-act="go" data-v="pedidos"><strong>${sep.length}</strong><span>Separados p/ retirada</span></button>
<button class="kpi" data-act="go" data-v="uso"><strong>${pecas}</strong><span>Peças em uso (${uso.length} cautelas)</span></button>
<button class="kpi ${atr.length?'alert':''}" data-act="go" data-v="uso"><strong>${atr.length}</strong><span>Cautelas em atraso</span></button></div>`;
if(D.setup&&D.setup.seed&&!D.setup.seeded)h+=`<div class="pend-box"><p>Carregando o catálogo inicial…</p></div>`;
if(pc.length)h+=`<div class="pend-box"><div class="row between"><p><b>${pc.length} cadastro(s) aguardando liberação</b></p><button class="btn btn-sm" data-act="go" data-v="militares">Ver</button></div></div>`;
const baixo=D.itens.filter(i=>i.ativo!==false&&(i.tamanhos||[]).some(t=>{const e=est(i,t);return e.total>0&&e.disp===0;}));
if(baixo.length)h+=`<div class="pend-box red"><p><b>Tamanhos esgotados na prateleira:</b> ${baixo.map(i=>esc(i.nome)+' ('+(i.tamanhos||[]).filter(t=>{const e=est(i,t);return e.total>0&&e.disp===0;}).map(esc).join(', ')+')').join('; ')}</p></div>`;
h+=`<div class="two"><div><div class="col-h"><h3>Pedidos novos</h3><span class="badge">${sol.length}</span></div>${sol.slice(0,8).map(c=>cardCautela(c,true)).join('')||'<div class="empty">Nenhum pedido novo.</div>'}</div>
<div><div class="col-h"><h3>Em atraso</h3><span class="badge red">${atr.length}</span></div>${atr.slice(0,8).map(c=>cardCautela(c,true)).join('')||'<div class="empty">Nenhuma cautela em atraso.</div>'}</div></div>`;
return h;
}
function vPedidos(){
const sol=solicitadas(),sep=separadas();
return `<div class="a-head"><div><h1>Pedidos</h1><p>Separe o material, o militar assina no celular e você confirma a entrega.</p></div><button class="btn btn-pri" data-act="balcao">+ Cautela no balcão</button></div>
<div class="cols"><div class="col"><div class="col-h"><h3>1. Novos</h3><span class="badge">${sol.length}</span></div>${sol.map(c=>cardCautela(c,true)).join('')||'<div class="empty">Nenhum.</div>'}</div>
<div class="col"><div class="col-h"><h3>2. Aguardando assinatura</h3><span class="badge">${sep.filter(c=>!c.assinatura).length}</span></div>${sep.filter(c=>!c.assinatura).map(c=>cardCautela(c,true)).join('')||'<div class="empty">Nenhum.</div>'}</div>
<div class="col"><div class="col-h"><h3>3. Assinados – entregar</h3><span class="badge">${sep.filter(c=>c.assinatura).length}</span></div>${sep.filter(c=>c.assinatura).map(c=>cardCautela(c,true)).join('')||'<div class="empty">Nenhum.</div>'}</div></div>`;
}
function vEmUso(){
const q=norm(ui.q);
let l=ativasA().filter(c=>!q||norm(nomeM(c.userId)+' '+turmaU(user(c.userId))+' '+itensTxt(c)+' '+c.num).includes(q));
l.sort((a,b)=>(atrasada(b)-atrasada(a))||String(a.prazo||'9').localeCompare(String(b.prazo||'9')));
return `<div class="a-head"><div><h1>Material em uso</h1><p>${l.length} cautela(s) ativas</p></div><button class="btn" data-act="csvUso">Exportar planilha (CSV)</button></div>
<div class="filters"><input class="i" data-inp="q" placeholder="Buscar por militar, pelotão, item ou nº" value="${esc(ui.q)}"></div>
<div class="tbl-wrap"><table><thead><tr><th>Nº</th><th>Militar</th><th>Material</th><th>Desde</th><th>Devolver até</th></tr></thead><tbody>
${l.map(c=>`<tr class="hov" data-act="ver" data-id="${c.id}"><td class="mono">${nr(c.num)}</td><td>${esc(nomeM(c.userId))}<br><span class="small muted">${esc(turmaU(user(c.userId)))}</span></td>
<td>${pendentes(c).map(x=>`${pend(x)}× ${esc(x.nome)}${tamTxt(x.tam)?' ('+esc(x.tam)+')':''}`).join('<br>')}</td><td>${fmtD(c.entregueEm||c.criadoEm)}</td>
<td>${c.prazo?`<span class="${atrasada(c)?'c-stamp':''}">${fmtD(c.prazo)}${atrasada(c)?' – em atraso':''}</span>`:'<span class="muted">sem prazo</span>'}${c.transferPara?'<br><span class="tag">em transferência</span>':''}</td></tr>`).join('')||'<tr><td colspan="5" class="muted">Nenhuma cautela ativa.</td></tr>'}
</tbody></table></div>`;
}

/* ----- Separação de um pedido ----- */
function opcoesTam(it,sel){return (it.tamanhos||[]).map(t=>`<option value="${esc(t)}" ${t===sel?'selected':''}>${esc(t)} – ${est(it,t).disp} disp.</option>`).join('');}
function separar(id){
const c=C(id);if(!c||c.status!=='solicitada')return;const u=user(c.userId);
openModal('Separar '+nr(c.num),`<form id="f-sep" data-id="${c.id}" class="stack">
<div class="ficha"><p style="font-weight:600">${esc(nomeU(u))}</p><p class="small muted">${esc(turmaU(u))}</p>${c.obs?`<p class="small">Obs.: ${esc(c.obs)}</p>`:''}
${u.romaneio&&Object.keys(u.romaneio).length?`<p class="small" style="margin-top:.4rem">Romaneio: ${Object.entries(u.romaneio).map(([k,v])=>esc((ROMN[k]||k).split(' ')[0])+' '+esc(v)).join(' · ')}</p>`:''}</div>
<div><span class="sep-lbl">Confira tamanho e quantidade de cada peça</span>
${(c.itens||[]).map((l,i)=>{const it=item(l.itemId);return `<div class="linha-item"><span class="nm">${esc(l.nome)}</span>
${(it.tamanhos||[]).length>1?`<select class="i" name="t${i}">${opcoesTam(it,l.tam)}</select>`:`<span class="small muted">${est(it,l.tam).disp} disp.</span>`}
<input class="i" type="number" name="q${i}" min="0" max="20" value="${l.qtd}" aria-label="Quantidade"><span class="small muted">0 = retirar</span></div>`;}).join('')}</div>
<label class="f"><span>Prazo de devolução (opcional)</span><input class="i" type="date" name="prazo"></label>
<label class="f"><span>Observação (opcional)</span><input class="i" name="obs"></label>
<p class="erro" id="sep-erro"></p></form>`,
`<button class="btn" data-act="fechar">Voltar</button><button class="btn btn-pri" data-act="confirmarSep" data-id="${c.id}">Separar e avisar o militar</button>`);
}
async function confirmarSep(id){
const c=C(id);const f=$('#f-sep');if(!c||!f)return;const fd=new FormData(f);
const linhas=(c.itens||[]).map((l,i)=>({...l,tam:fd.get('t'+i)!=null?String(fd.get('t'+i)):l.tam,qtd:int(fd.get('q'+i))})).filter(l=>l.qtd>0);
if(!linhas.length){$('#sep-erro').textContent='Nenhuma peça para separar. Para negar o pedido, use "Recusar".';return;}
const prazo=prazoDe(fd.get('prazo'));const obs=String(fd.get('obs')||'').trim();
try{await separarEstoque(c.id,linhas,'solicitada',{prazo,status:'separada'},'Separada',obs);closeModal();toast(`${nr(c.num)} separada. O militar foi avisado.`);}
catch(e){console.error(e);$('#sep-erro').textContent=erroFirebase(e);}
}
/* Baixa o disponível de cada tamanho e grava a cautela, numa transação única */
async function separarEstoque(cautId,linhas,statusEsperado,extra,acao,obs){
await runTransaction(db,async tx=>{
const cref=doc(db,'cautelas',cautId);const cs=await tx.get(cref);const o=cs.data();
if(!o||o.status!==statusEsperado)throw {msg:'Este pedido mudou de situação (talvez o militar tenha cancelado). Feche e confira.'};
const ids=[...new Set(linhas.map(l=>l.itemId))];const snaps={};
for(const iid of ids){snaps[iid]=(await tx.get(doc(db,'itens',iid))).data();}
const falta=[];
ids.forEach(iid=>{const it=snaps[iid];const e=JSON.parse(JSON.stringify(it.estoque||{}));
linhas.filter(l=>l.itemId===iid).forEach(l=>{const x=e[l.tam]||{total:0,disp:0};if(x.disp<l.qtd)falta.push(`${it.nome}${tamTxt(l.tam)?' ('+l.tam+')':''}: só ${x.disp}`);x.disp-=l.qtd;e[l.tam]=x;});
snaps[iid]._novo=e;});
if(falta.length)throw {msg:'Estoque insuficiente – '+falta.join('; ')};
ids.forEach(iid=>tx.update(doc(db,'itens',iid),{estoque:snaps[iid]._novo}));
tx.update(cref,{...extra,itens:linhas,atualizadoEm:nowISO(),separadoPor:sess.userId,log:[...(o.log||[]),entrada(acao,obs)]});
});
}
function recusar(id){
const c=C(id);if(!c)return;
openModal('Recusar '+nr(c.num),`<form id="f-recusar" data-id="${c.id}" class="stack"><label class="f"><span>Motivo (o militar vai ver)</span><textarea class="i" name="m" required placeholder="Ex.: sem estoque do tamanho; procure o almoxarifado"></textarea></label><button class="btn btn-warn btn-block">Recusar pedido</button></form>`);
}
async function confirmarRecusa(form,fd){
const c=C(form.dataset.id);if(!c)return;
await updateDoc(doc(db,'cautelas',c.id),{status:'recusada',atualizadoEm:nowISO(),log:[...(c.log||[]),entrada('Recusada',String(fd.get('m')||''))]});closeModal();toast('Pedido recusado.');
}
async function cancelarSep(id){
const c=C(id);if(!c||c.status!=='separada')return;
if(!confirm('Cancelar esta cautela e devolver as peças ao estoque?'))return;
try{await runTransaction(db,async tx=>{const cref=doc(db,'cautelas',id);const o=(await tx.get(cref)).data();if(!o||o.status!=='separada')throw {msg:'A cautela mudou de situação.'};
const ids=[...new Set(o.itens.map(l=>l.itemId))];const sn={};for(const iid of ids)sn[iid]=(await tx.get(doc(db,'itens',iid))).data();
ids.forEach(iid=>{const e=JSON.parse(JSON.stringify(sn[iid].estoque||{}));o.itens.filter(l=>l.itemId===iid).forEach(l=>{const x=e[l.tam]||{total:0,disp:0};x.disp+=l.qtd;e[l.tam]=x;});tx.update(doc(db,'itens',iid),{estoque:e});});
tx.update(cref,{status:'cancelada',atualizadoEm:nowISO(),log:[...(o.log||[]),entrada('Cancelada pelo almoxarifado','Peças devolvidas ao estoque')]});});
closeModal();toast('Cautela cancelada e estoque devolvido.');}catch(e){toast(erroFirebase(e),true);}
}
async function entregar(id){
const c=C(id);if(!c||c.status!=='separada'||!c.assinatura)return;
try{await runTransaction(db,async tx=>{const cref=doc(db,'cautelas',id);const o=(await tx.get(cref)).data();if(!o||o.status!=='separada'||!o.assinatura)throw {msg:'A cautela mudou de situação.'};
const cons=o.itens.filter(l=>l.consumo);const ids=[...new Set(cons.map(l=>l.itemId))];const sn={};for(const iid of ids)sn[iid]=(await tx.get(doc(db,'itens',iid))).data();
ids.forEach(iid=>{const e=JSON.parse(JSON.stringify(sn[iid].estoque||{}));cons.filter(l=>l.itemId===iid).forEach(l=>{const x=e[l.tam]||{total:0,disp:0};x.total=Math.max(0,x.total-l.qtd);e[l.tam]=x;});tx.update(doc(db,'itens',iid),{estoque:e});});
const final=o.itens.every(l=>l.consumo);
tx.update(cref,{status:final?'concluida':'cautelada',entregueEm:nowISO(),entreguePor:sess.userId,atualizadoEm:nowISO(),log:[...(o.log||[]),entrada(final?'Entregue (definitivo)':'Cautelada','Entrega confirmada pelo almoxarifado')]});});
closeModal();toast(`${nr(c.num)} entregue.`);}catch(e){toast(erroFirebase(e),true);}
}
/* A senha do militar digitada no aparelho do almoxarifado confirma a identidade sem trocar a sessão atual */
async function comAuthSecundario(fn){
const app2=initializeApp(FB,'sec-'+Date.now());const a2=initializeAuth(app2,{persistence:inMemoryPersistence});
try{return await fn(a2);}finally{try{await signOut(a2);}catch(e){} try{await deleteApp(app2);}catch(e){}}
}
function assBalcao(id){
const c=C(id);if(!c)return;const u=user(c.userId);
openModal('Assinatura no balcão – '+nr(c.num),`<form id="f-assbal" data-id="${c.id}" class="stack">
<div class="ficha"><p style="font-weight:600">${esc(nomeU(u))}</p>${itensLi(c)}<dl class="meta"><dt>Devolver até</dt><dd>${c.prazo?fmtD(c.prazo):'sem prazo definido'}</dd></dl></div>
<p class="aviso">Entregue o aparelho ao militar. Ao digitar a senha, ${esc(nomeU(u))} declara que recebeu o material acima, conferiu tamanhos e quantidades e se responsabiliza pela guarda e devolução.</p>
<label class="f"><span>Senha do Almox EsFO de ${esc(nomeU(u))}</span><input class="i" type="password" name="s" required autocomplete="off"></label>
<p class="erro" id="assbal-erro"></p><button class="btn btn-pri btn-block">Assinar e entregar</button>
<p class="small muted">Ou feche esta janela: o militar também pode assinar no próprio celular, em "Início".</p></form>`);
}
async function confirmarAssBalcao(form,fd){
const c=C(form.dataset.id);const u=user(c.userId);
try{await comAuthSecundario(a2=>signInWithEmailAndPassword(a2,u.email,String(fd.get('s'))));}
catch(e){$('#assbal-erro').textContent=e.code==='auth/too-many-requests'?erroFirebase(e):'Senha incorreta. Peça ao militar para digitar de novo.';return;}
const em=nowISO();const dados=`ALMOX ESFO | Recebimento (balcão) | Cautela ${nr(c.num)} | ${nomeU(u)} | Material: ${itensTxt(c)} | Prazo: ${c.prazo?fmtD(c.prazo):'sem prazo'} | ${em}`;
const ass={por:c.userId,em,metodo:'balcao',dados,hash:await hashTexto(dados),registradoPor:sess.userId,aparelho:navigator.userAgent.slice(0,160)};
try{await updateDoc(doc(db,'cautelas',c.id),{assinatura:ass,log:[...(c.log||[]),{t:em,a:'Assinada',por:c.userId,obs:FORMA.balcao}]});
D.cautelas=D.cautelas.map(x=>x.id===c.id?{...x,assinatura:ass}:x);await entregar(c.id);}
catch(e){$('#assbal-erro').textContent=erroFirebase(e);}
}

/* ----- Cautela no balcão ----- */
function abrirBalcao(){
ui.bal={userId:'',linhas:[],q:''};desenharBalcao();
}
function desenharBalcao(){
const b=ui.bal;const u=b.userId?user(b.userId):null;
const mil=D.users.filter(x=>x.ativo).sort((a,c)=>nomeU(a).localeCompare(nomeU(c),'pt-BR'));
const its=ordenarItens(D.itens.filter(i=>i.ativo!==false).slice());
openModal('Cautela no balcão',`<form id="f-bal" class="stack" autocomplete="off">
<label class="f"><span>Militar</span><select class="i" name="mil" data-chg="balMil"><option value="">Escolha…</option>${mil.map(x=>`<option value="${x.id}" ${x.id===b.userId?'selected':''}>${esc(nomeU(x))} – ${esc(turmaU(x))}</option>`).join('')}</select></label>
${u&&u.romaneio&&Object.keys(u.romaneio).length?`<p class="small">Romaneio: ${Object.entries(u.romaneio).map(([k,v])=>esc((ROMN[k]||k).split(' ')[0])+' '+esc(v)).join(' · ')}</p>`:''}
<div class="dupla stack"><div class="grid2"><label class="f"><span>Item</span><select class="i" name="it" data-chg="balIt"><option value="">Escolha…</option>${its.map(i=>`<option value="${i.id}" ${i.id===b.it?'selected':''}>${esc(cat(i.catId).nome)} – ${esc(i.nome)}</option>`).join('')}</select></label>
<label class="f"><span>Tamanho</span><select class="i" name="tam">${b.it?opcoesTam(item(b.it),sugTam(item(b.it),u)||(item(b.it).tamanhos||[]).find(t=>est(item(b.it),t).disp>0)||(item(b.it).tamanhos||[])[0]):''}</select></label></div>
<div class="row"><label class="f" style="flex:1"><span>Quantidade</span><input class="i" type="number" name="qtd" min="1" max="20" value="1"></label><button type="button" class="btn" data-act="balAdd" style="margin-top:1.2rem">Adicionar</button></div></div>
<ul class="bal-lista">${b.linhas.map((l,i)=>`<li><span class="nm">${l.qtd}× ${esc(l.nome)}${tamTxt(l.tam)?` <span class="tag">${esc(l.tam)}</span>`:''}</span><button type="button" class="mini rm" data-act="balRm" data-i="${i}">×</button></li>`).join('')||'<li class="muted small">Nenhuma peça adicionada.</li>'}</ul>
<div class="grid2"><label class="f"><span>Prazo de devolução (opcional)</span><input class="i" type="date" name="prazo" value="${esc(b.prazo||'')}" data-chg="balPrazo"></label>
<label class="f"><span>Observação</span><input class="i" name="obs" value="${esc(b.obs||'')}" data-chg="balObs"></label></div>
<p class="erro" id="bal-erro"></p></form>`,
`<button class="btn" data-act="fechar">Cancelar</button><button class="btn btn-pri" data-act="balGravar" ${b.userId&&b.linhas.length?'':'disabled'}>Separar e assinar</button>`,
'O estoque é baixado agora. Depois o militar assina com a senha aqui ou no próprio celular.');
}
function balAdd(){
const f=$('#f-bal');const fd=new FormData(f);const b=ui.bal;
const iid=String(fd.get('it')||'');if(!iid){$('#bal-erro').textContent='Escolha o item.';return;}
const it=item(iid);const tam=String(fd.get('tam')||(it.tamanhos||[])[0]||'Único');const q=Math.max(1,int(fd.get('qtd')));
const ja=b.linhas.filter(l=>l.itemId===iid&&l.tam===tam).reduce((a,l)=>a+l.qtd,0);
if(est(it,tam).disp<ja+q){$('#bal-erro').textContent=`Só há ${est(it,tam).disp} disponível(is) de ${it.nome}${tamTxt(tam)?' ('+tam+')':''}.`;return;}
const x=b.linhas.find(l=>l.itemId===iid&&l.tam===tam);
if(x)x.qtd+=q;else b.linhas.push({itemId:iid,nome:it.nome,tam,qtd:q,dev:0,trf:0,consumo:!!it.consumo,unidade:it.unidade||'un'});
b.it='';desenharBalcao();
}
async function balGravar(){
const b=ui.bal;if(!b.userId||!b.linhas.length)return;
const btn=$$('.mf .btn-pri')[0];if(btn){btn.disabled=true;btn.textContent='Gravando…';}
try{
let novoId=null;
await runTransaction(db,async tx=>{
const ids=[...new Set(b.linhas.map(l=>l.itemId))];const sn={};for(const iid of ids)sn[iid]=(await tx.get(doc(db,'itens',iid))).data();
const num=await proxNumero(tx);
const falta=[];ids.forEach(iid=>{const e=JSON.parse(JSON.stringify(sn[iid].estoque||{}));b.linhas.filter(l=>l.itemId===iid).forEach(l=>{const x=e[l.tam]||{total:0,disp:0};if(x.disp<l.qtd)falta.push(`${l.nome} (${l.tam}): só ${x.disp}`);x.disp-=l.qtd;e[l.tam]=x;});sn[iid]._e=e;});
if(falta.length)throw {msg:'Estoque insuficiente – '+falta.join('; ')};
ids.forEach(iid=>tx.update(doc(db,'itens',iid),{estoque:sn[iid]._e}));
const ref=doc(collection(db,'cautelas'));novoId=ref.id;
tx.set(ref,{num,userId:b.userId,origem:'balcao',status:'separada',itens:b.linhas,obs:b.obs||'',prazo:prazoDe(b.prazo),assinatura:null,transferPara:null,transfer:null,
criadoEm:nowISO(),atualizadoEm:nowISO(),separadoPor:sess.userId,log:[entrada('Cautela aberta no balcão',b.obs||'')]});
});
ui.bal=null;
const esperar=Date.now();const t=setInterval(()=>{if(C(novoId)||Date.now()-esperar>8000){clearInterval(t);if(C(novoId))assBalcao(novoId);else closeModal();}},200);
}catch(e){console.error(e);const el=$('#bal-erro');if(el)el.textContent=erroFirebase(e);if(btn){btn.disabled=false;btn.textContent='Separar e assinar';}}
}

/* ----- Devolução ----- */
function devolver(id){
const c=C(id);if(!c)return;const u=user(c.userId);
const ls=(c.itens||[]).map((l,i)=>({l,i})).filter(x=>pend(x.l)>0);
openModal('Devolução – '+nr(c.num),`<form id="f-dev" data-id="${c.id}" class="stack"><p><b>${esc(nomeU(u))}</b> <span class="small muted">${esc(turmaU(u))}</span></p>
${ls.map(({l,i})=>`<div class="linha-item"><span class="nm">${esc(l.nome)}${tamTxt(l.tam)?` <span class="tag">${esc(l.tam)}</span>`:''} <span class="small muted">(${pend(l)} em uso)</span></span>
<input class="i" type="number" name="q${i}" min="0" max="${pend(l)}" value="${pend(l)}" aria-label="Quantidade devolvida">
<select class="i estado-sel" name="e${i}"><option value="bom">Em bom estado</option><option value="danificado">Danificado / inservível</option><option value="extraviado">Extraviado (não devolvido)</option></select></div>`).join('')}
<label class="f"><span>Observação (obrigatória se houver dano ou extravio)</span><input class="i" name="obs"></label>
<p class="small muted">Peças em bom estado voltam para a prateleira. Danificadas ou extraviadas saem do estoque e ficam registradas como ocorrência.</p>
<p class="erro" id="dev-erro"></p></form>`,`<button class="btn" data-act="fechar">Voltar</button><button class="btn btn-pri" data-act="confirmarDev" data-id="${c.id}">Registrar devolução</button>`);
}
async function confirmarDev(id){
const c=C(id);const f=$('#f-dev');if(!c||!f)return;const fd=new FormData(f);const obs=String(fd.get('obs')||'').trim();
const mov=(c.itens||[]).map((l,i)=>({i,q:Math.min(int(fd.get('q'+i)),pend(l)),e:String(fd.get('e'+i)||'bom')})).filter(x=>x.q>0);
if(!mov.length){$('#dev-erro').textContent='Informe a quantidade devolvida.';return;}
if(mov.some(x=>x.e!=='bom')&&!obs){$('#dev-erro').textContent='Descreva o dano ou o extravio na observação.';return;}
try{await runTransaction(db,async tx=>{const cref=doc(db,'cautelas',id);const o=(await tx.get(cref)).data();if(!o||o.status!=='cautelada')throw {msg:'A cautela mudou de situação.'};
const itens=o.itens.map(l=>({...l}));const ids=[...new Set(mov.map(x=>itens[x.i].itemId))];const sn={};for(const iid of ids)sn[iid]=(await tx.get(doc(db,'itens',iid))).data();
const ocorr=[...(o.ocorrencias||[])];const em=nowISO();
ids.forEach(iid=>{sn[iid]._e=JSON.parse(JSON.stringify(sn[iid].estoque||{}));});
mov.forEach(x=>{const l=itens[x.i];const q=Math.min(x.q,pend(l));if(q<=0)return;l.dev=(l.dev||0)+q;const e=sn[l.itemId]._e;const s=e[l.tam]||{total:0,disp:0};
if(x.e==='bom')s.disp+=q;else{s.total=Math.max(0,s.total-q);ocorr.push({t:em,nome:l.nome,tam:l.tam,qtd:q,estado:x.e,obs,por:sess.userId});}e[l.tam]=s;});
ids.forEach(iid=>tx.update(doc(db,'itens',iid),{estoque:sn[iid]._e}));
const resta=itens.some(l=>pend(l)>0);
const txt=mov.map(x=>`${x.q}× ${itens[x.i].nome}${tamTxt(itens[x.i].tam)?' ('+itens[x.i].tam+')':''}${x.e!=='bom'?' – '+x.e:''}`).join(', ');
tx.update(cref,{itens,ocorrencias:ocorr,status:resta?'cautelada':'devolvida',atualizadoEm:em,...(resta?{}:{devolvidaEm:em}),log:[...(o.log||[]),entrada(resta?'Devolução parcial':'Devolvida',txt+(obs?' | '+obs:''))]});
mov.filter(x=>x.e!=='bom').forEach(x=>{tx.set(doc(collection(db,'movimentos')),{t:em,tipo:'ocorrencia',itemId:itens[x.i].itemId,nome:itens[x.i].nome,tam:itens[x.i].tam,qtd:x.q,motivo:x.e,obs,cautela:id,num:o.num,userId:o.userId,por:sess.userId});});
});closeModal();toast('Devolução registrada.');}catch(e){console.error(e);$('#dev-erro').textContent=erroFirebase(e);}
}
function editarPrazo(id){
const c=C(id);if(!c)return;
openModal('Prazo de devolução – '+nr(c.num),`<form id="f-prazo" data-id="${c.id}" class="stack"><label class="f"><span>Devolver até (deixe em branco para sem prazo)</span><input class="i" type="date" name="p" value="${dataInput(c.prazo)}"></label><button class="btn btn-pri btn-block">Salvar prazo</button></form>`);
}
async function salvarPrazo(form,fd){
const c=C(form.dataset.id);const p=prazoDe(fd.get('p'));
await updateDoc(doc(db,'cautelas',c.id),{prazo:p,atualizadoEm:nowISO(),log:[...(c.log||[]),entrada('Prazo alterado',p?'Até '+fmtD(p):'Sem prazo')]});closeModal();toast('Prazo salvo.');
}

/* ============ Material: categorias, itens, tamanhos e estoque ============ */
function resumoCat(c){
const its=D.itens.filter(i=>i.catId===c.id);let tot=0,dis=0,uso=0,esg=0;
its.forEach(it=>(it.tamanhos||[]).forEach(t=>{const e=est(it,t);tot+=e.total;dis+=e.disp;uso+=cauteladoDe(it.id,t);if(e.total>0&&e.disp<=0)esg++;}));
return {n:its.length,tot,dis,uso,esg};
}
function vMaterial(){
const q=norm(ui.matQ);
if(ui.matCat&&!D.cats.some(c=>c.id===ui.matCat))ui.matCat=null;
if(ui.matCat&&!q)return vMaterialCat(D.cats.find(c=>c.id===ui.matCat));
let h=`<div class="a-head"><div><h1>Material</h1><p>Escolha uma categoria para ver os itens, os tamanhos e o estoque.</p></div>
<div class="row"><button class="btn" data-act="importar">Importar planilha (Excel)</button><button class="btn" data-act="novaCat">+ Categoria</button><button class="btn btn-pri" data-act="novoItem">+ Item</button></div></div>
<div class="filters"><input class="i" data-inp="matQ" placeholder="Buscar item em todas as categorias" value="${esc(ui.matQ)}"></div>`;
if(q){const its=D.itens.filter(i=>norm(i.nome).includes(q));
return h+(its.length?`<div class="it-lista">${its.map(rowItem).join('')}</div>`:'<div class="empty">Nenhum item encontrado.</div>');}
if(!D.cats.length)return h+`<div class="empty">Nenhuma categoria. Crie a primeira em "+ Categoria".</div>`;
h+=`<div class="cat-grid2">${D.cats.map(c=>{const r=resumoCat(c);return `<button class="cat-tile" data-act="matCat" data-id="${c.id}">
<span class="cat-ic">${svgCat(icCat(c))}</span><h3>${esc(c.nome)}</h3>
<span class="n">${r.n} ${r.n===1?'item':'itens'} · <b>${r.dis}</b> na prateleira${r.uso?` · ${r.uso} em uso`:''}${r.esg?`<br><span class="alerta">${r.esg} tamanho(s) esgotado(s)</span>`:''}</span></button>`;}).join('')}</div>`;
const sem=D.itens.filter(i=>!D.cats.some(c=>c.id===i.catId));
if(sem.length)h+=`<div class="sec-h"><h2>Sem categoria</h2></div><div class="it-lista">${sem.map(rowItem).join('')}</div>`;
return h;
}
function rowItem(it){
const tams=it.tamanhos||[];
const tot=tams.reduce((a,t)=>a+est(it,t).total,0),dis=tams.reduce((a,t)=>a+est(it,t).disp,0),uso=tams.reduce((a,t)=>a+cauteladoDe(it.id,t),0);
const unico=tams.length<=1;
return `<div class="it-row"><div><h3>${esc(it.nome)}${it.ativo===false?' <span class="tag">fora do app</span>':''}${it.consumo?' <span class="tag">entrega definitiva</span>':''}</h3>
<p class="resumo"><b>${dis}</b> na prateleira · ${uso} em uso · total ${tot} ${esc((UNID[it.unidade]||UNID.un)[tot===1?0:1])}${it.campo?` · tamanho pelo romaneio (${esc((ROMN[it.campo]||it.campo).split(' (')[0])})`:''}</p></div>
<div class="acts"><button class="btn btn-sm btn-pri" data-act="entrada" data-id="${it.id}">Entrada</button><button class="btn btn-sm" data-act="ajuste" data-id="${it.id}">Baixa / inventário</button><button class="btn btn-sm" data-act="quem" data-id="${it.id}">Com quem está</button><button class="btn btn-sm" data-act="editItem" data-id="${it.id}">Editar</button></div>
${unico?'':`<div class="tams">${tams.map(t=>{const e=est(it,t),u=cauteladoDe(it.id,t);return `<span class="tam-chip${e.total>0&&e.disp<=0?' zero':''}" title="${e.disp} na prateleira, ${u} em uso, total ${e.total}">${esc(t)} <b>${e.disp}</b>${u?`<span class="u">+${u} em uso</span>`:''}</span>`;}).join('')}</div>`}</div>`;
}
function vMaterialCat(c){
const its=D.itens.filter(i=>i.catId===c.id);const r=resumoCat(c);
return `<button class="voltar" data-act="matCat" data-id="">← Todas as categorias</button>
<div class="cat-topo"><span class="cat-ic">${svgCat(icCat(c))}</span><div style="flex:1;min-width:10rem"><h1>${esc(c.nome)}</h1><p class="muted">${r.n} ${r.n===1?'item':'itens'} · ${r.dis} na prateleira · ${r.uso} em uso · total ${r.tot}</p></div>
<div class="row"><button class="btn" data-act="importar">Importar planilha</button><button class="btn" data-act="editCat" data-id="${c.id}">Editar categoria</button><button class="btn btn-pri" data-act="novoItem" data-cat="${c.id}">+ Item nesta categoria</button></div></div>
<p class="small muted" style="margin-bottom:.6rem">Os números grandes mostram quantas peças de cada tamanho estão na prateleira.</p>
${its.length?`<div class="it-lista">${its.map(rowItem).join('')}</div>`:'<div class="empty">Nenhum item nesta categoria.</div>'}`;
}
function formCat(c){
c=c||{};const atual=c.id?icCat(c):'generico';
openModal(c.id?'Editar categoria':'Nova categoria',`<form id="f-cat" data-id="${c.id||''}" class="stack">
<label class="f"><span>Nome</span><input class="i" name="nome" required value="${esc(c.nome||'')}"></label>
<div><span class="sep-lbl">Imagem da categoria</span><div class="ic-esc">${Object.entries(CAT_IC).map(([k,v])=>`<label><input type="radio" name="icone" value="${k}" ${k===atual?'checked':''}>${svgCat(k)}<span>${v[0]}</span></label>`).join('')}</div></div>
<label class="f"><span>Ordem na lista</span><input class="i" type="number" name="ordem" value="${c.ordem!=null?c.ordem:(D.cats.length+1)*10}"></label>
<button class="btn btn-pri btn-block">Salvar</button></form>`);
}
async function salvarCat(form,fd){
const id=form.dataset.id||uidNovo();
await setDoc(doc(db,'categorias',id),{nome:String(fd.get('nome')).trim(),ordem:int(fd.get('ordem')),icone:String(fd.get('icone')||'generico')},{merge:true});closeModal();toast('Categoria salva.');
}
function formItem(it,catPadrao){
it=it||{catId:catPadrao};
openModal(it.id?'Editar item':'Novo item',`<form id="f-item" data-id="${it.id||''}" class="stack">
<label class="f"><span>Categoria</span><select class="i" name="catId" required>${D.cats.map(c=>`<option value="${c.id}" ${c.id===it.catId?'selected':''}>${esc(c.nome)}</option>`).join('')}</select></label>
<label class="f"><span>Nome do item</span><input class="i" name="nome" required value="${esc(it.nome||'')}" placeholder="Ex.: Luva branca"></label>
<div class="grid2"><label class="f"><span>Unidade</span><select class="i" name="unidade">${Object.entries(UNID).map(([k,v])=>`<option value="${k}" ${it.unidade===k?'selected':''}>${v[0]}</option>`).join('')}</select></label>
<label class="f"><span>Sugerir tamanho pelo romaneio</span><select class="i" name="campo"><option value="">Não (tamanho único ou livre)</option>${ROM.map(([k,n])=>`<option value="${k}" ${it.campo===k?'selected':''}>${n}</option>`).join('')}</select></label></div>
<label class="f"><span>Tamanhos, separados por vírgula</span><input class="i" name="tamanhos" value="${esc((it.tamanhos||['Único']).join(', '))}" placeholder="Ex.: P, M, G, GG – ou: Único"></label>
<label class="check"><input type="checkbox" name="consumo" ${it.consumo?'checked':''}><span>Entrega definitiva (o militar não devolve; ex.: material de consumo)</span></label>
<label class="check"><input type="checkbox" name="ativo" ${it.ativo===false?'':'checked'}><span>Disponível para pedidos pelo app</span></label>
<p class="erro" id="item-erro"></p><button class="btn btn-pri btn-block">Salvar item</button></form>`);
}
async function salvarItem(form,fd){
const id=form.dataset.id;const ant=id?item(id):null;
let tams=String(fd.get('tamanhos')||'').split(',').map(s=>s.trim().toUpperCase()).filter(Boolean);
tams=[...new Set(tams.map(t=>norm(t)==='unico'?'Único':t))];if(!tams.length)tams=['Único'];
const estoque={...((ant&&ant.estoque)||{})};
if(ant){const presos=(ant.tamanhos||[]).filter(t=>!tams.includes(t)&&(est(ant,t).total>0||cauteladoDe(id,t)>0));
if(presos.length){$('#item-erro').textContent='Não dá para remover tamanho com estoque ou em uso: '+presos.join(', ')+'. Faça a baixa antes.';return;}
Object.keys(estoque).forEach(t=>{if(!tams.includes(t))delete estoque[t];});}
tams.forEach(t=>{if(!estoque[t])estoque[t]={total:0,disp:0};});
const o={catId:String(fd.get('catId')),nome:String(fd.get('nome')).trim(),unidade:String(fd.get('unidade')),campo:String(fd.get('campo')||''),tamanhos:tams,estoque,consumo:!!fd.get('consumo'),ativo:!!fd.get('ativo')};
if(!ant)o.ordem=D.itens.filter(i=>i.catId===o.catId).length*10;
await setDoc(doc(db,'itens',id||uidNovo()),o,{merge:false});closeModal();toast('Item salvo.');
}
function formEntrada(id){
const it=item(id);
openModal('Entrada – '+esc(it.nome),`<form id="f-ent" data-id="${id}" class="stack">
<p class="small muted">Informe quantas peças estão chegando em cada tamanho (compra, doação, recolhimento…).</p>
<div class="estq">${(it.tamanhos||[]).map(t=>`<label class="f"><span>${esc(t)} <span class="muted">(${est(it,t).disp} disp.)</span></span><input class="i" type="number" min="0" name="t_${esc(t)}" value="0"></label>`).join('')}</div>
<label class="f"><span>Origem / documento</span><input class="i" name="obs" required placeholder="Ex.: Nota de transferência nº 12/2026"></label>
<p class="erro" id="ent-erro"></p><button class="btn btn-pri btn-block">Registrar entrada</button></form>`);
}
async function salvarEntrada(form,fd){
const id=form.dataset.id;const it=item(id);const add={};(it.tamanhos||[]).forEach(t=>{const q=int(fd.get('t_'+t));if(q>0)add[t]=q;});
if(!Object.keys(add).length){$('#ent-erro').textContent='Informe pelo menos uma quantidade.';return;}
const obs=String(fd.get('obs')||'').trim();
await runTransaction(db,async tx=>{const r=doc(db,'itens',id);const o=(await tx.get(r)).data();const e=JSON.parse(JSON.stringify(o.estoque||{}));
Object.entries(add).forEach(([t,q])=>{const x=e[t]||{total:0,disp:0};x.total+=q;x.disp+=q;e[t]=x;});tx.update(r,{estoque:e});
tx.set(doc(collection(db,'movimentos')),{t:nowISO(),tipo:'entrada',itemId:id,nome:o.nome,tams:add,obs,por:sess.userId});});
closeModal();toast('Entrada registrada.');
}
function formAjuste(id){
const it=item(id);
openModal('Baixa / inventário – '+esc(it.nome),`<form id="f-aj" data-id="${id}" class="stack">
<div class="seg" role="group"><button type="button" data-act="ajModo" data-m="baixa" aria-pressed="${(ui.ajModo||'baixa')==='baixa'}">Baixa de peças</button><button type="button" data-act="ajModo" data-m="inv" aria-pressed="${ui.ajModo==='inv'}">Contagem (inventário)</button></div>
${(ui.ajModo||'baixa')==='baixa'
?`<p class="small muted">Retira da prateleira peças inservíveis, perdidas ou descartadas.</p><div class="estq">${(it.tamanhos||[]).map(t=>`<label class="f"><span>${esc(t)} <span class="muted">(${est(it,t).disp} disp.)</span></span><input class="i" type="number" min="0" max="${est(it,t).disp}" name="t_${esc(t)}" value="0"></label>`).join('')}</div>
<label class="f"><span>Motivo</span><select class="i" name="motivo"><option>Inservível</option><option>Extravio</option><option>Descarte</option><option>Outro</option></select></label>`
:`<p class="small muted">Digite quantas peças você contou na prateleira (sem contar as que estão com os militares). O sistema ajusta a diferença.</p><div class="estq">${(it.tamanhos||[]).map(t=>`<label class="f"><span>${esc(t)} <span class="muted">(sistema: ${est(it,t).disp})</span></span><input class="i" type="number" min="0" name="t_${esc(t)}" value="${est(it,t).disp}"></label>`).join('')}</div>`}
<label class="f"><span>Observação</span><input class="i" name="obs" required></label>
<input type="hidden" name="modo" value="${ui.ajModo||'baixa'}">
<p class="erro" id="aj-erro"></p><button class="btn btn-pri btn-block">Registrar</button></form>`);
}
async function salvarAjuste(form,fd){
const id=form.dataset.id;const it=item(id);const modo=fd.get('modo');const obs=String(fd.get('obs')||'').trim();const ch={};
(it.tamanhos||[]).forEach(t=>{const v=int(fd.get('t_'+t));if(modo==='baixa'){if(v>0)ch[t]=v;}else if(v!==est(it,t).disp)ch[t]=v;});
if(!Object.keys(ch).length){$('#aj-erro').textContent='Nenhuma alteração.';return;}
try{await runTransaction(db,async tx=>{const r=doc(db,'itens',id);const o=(await tx.get(r)).data();const e=JSON.parse(JSON.stringify(o.estoque||{}));const reg={};
Object.entries(ch).forEach(([t,v])=>{const x=e[t]||{total:0,disp:0};
if(modo==='baixa'){if(v>x.disp)throw {msg:`Só há ${x.disp} disponível(is) no tamanho ${t}.`};x.disp-=v;x.total-=v;reg[t]=-v;}
else{const d=v-x.disp;x.disp=v;x.total=Math.max(0,x.total+d);reg[t]=d;}e[t]=x;});
tx.update(r,{estoque:e});tx.set(doc(collection(db,'movimentos')),{t:nowISO(),tipo:modo==='baixa'?'baixa':'inventario',motivo:modo==='baixa'?String(fd.get('motivo')):'',itemId:id,nome:o.nome,tams:reg,obs,por:sess.userId});});
closeModal();toast('Registrado.');}catch(e){$('#aj-erro').textContent=erroFirebase(e);}
}
function quemEsta(id){
const it=item(id);const l=[];
ativasA().forEach(c=>(c.itens||[]).forEach(x=>{if(x.itemId===id&&pend(x)>0)l.push({c,x});}));
openModal('Com quem está – '+esc(it.nome),l.length?`<div class="tbl-wrap"><table><thead><tr><th>Militar</th><th>Tam.</th><th>Qtd</th><th>Nº</th><th>Prazo</th></tr></thead><tbody>${l.map(({c,x})=>`<tr class="hov" data-act="ver" data-id="${c.id}"><td>${esc(nomeM(c.userId))}<br><span class="small muted">${esc(turmaU(user(c.userId)))}</span></td><td>${esc(x.tam)}</td><td>${pend(x)}</td><td class="mono">${nr(c.num)}</td><td>${c.prazo?fmtD(c.prazo):'—'}</td></tr>`).join('')}</tbody></table></div>`:'<div class="empty">Nenhuma peça deste item está cautelada.</div>');
}

/* ============ Militares ============ */
function vMilitares(){
const q=norm(ui.mq);const pc=pendCad();
let l=D.users.filter(u=>!u.pendente&&(!q||norm(nomeU(u)+' '+u.nome+' '+turmaU(u)+' '+u.email+' '+(u.rg||'')).includes(q)));
l.sort((a,b)=>(b.ativo-a.ativo)||nomeU(a).localeCompare(nomeU(b),'pt-BR'));
const emUso=id=>ativasA().filter(c=>c.userId===id).reduce((a,c)=>a+(c.itens||[]).reduce((b,x)=>b+pend(x),0),0);
let h=`<div class="a-head"><div><h1>Militares</h1><p>${D.users.filter(u=>u.ativo).length} com acesso liberado</p></div><div class="row"><button class="btn" data-act="csvMil">Exportar romaneios (CSV)</button><button class="btn btn-pri" data-act="novoMil">+ Cadastrar oficial de fora da EsFO</button></div></div>`;
if(pc.length)h+=`<div class="sec-h"><h2>Aguardando liberação</h2></div>`+pc.map(u=>`<div class="card" style="margin-bottom:.6rem"><div class="card-t"><div><p style="font-weight:600">${esc(nomeU(u))} <span class="tag">${u.perfil==='almox'?'Conta do almoxarifado':u.tipo==='oficial'?'Oficial':'Cadete'}</span></p>
<p class="small muted">${esc(u.nome)} · ${esc(u.email)}</p><p class="small muted">Cadastro em ${fmt(u.criadoEm)}</p></div>
<div class="row"><button class="btn btn-sm btn-warn" data-act="negarCad" data-id="${u.id}">Recusar</button><button class="btn btn-sm btn-pri" data-act="liberar" data-id="${u.id}">Liberar</button></div></div></div>`).join('');
h+=`<div class="filters" style="margin-top:1rem"><input class="i" data-inp="mq" placeholder="Buscar por nome, pelotão, RG ou e-mail" value="${esc(ui.mq)}"></div>
<div class="tbl-wrap"><table><thead><tr><th>Militar</th><th>Turma / OPM</th><th>Peças em uso</th><th>Situação</th></tr></thead><tbody>
${l.map(u=>`<tr class="hov" data-act="verMil" data-id="${u.id}"><td>${esc(nomeU(u))}<br><span class="small muted">${esc(u.nome)}</span></td><td>${esc(turmaU(u))||'<span class="muted">dados incompletos</span>'}</td><td>${emUso(u.id)||'—'}</td>
<td>${u.perfil==='almox'?'<span class="tag">Almoxarifado</span> ':''}${u.externo?'<span class="tag">Oficial externo</span> ':''}${u.ativo?'<span class="pill ok">Ativo</span>':'<span class="pill no">Sem acesso</span>'}</td></tr>`).join('')||'<tr><td colspan="4" class="muted">Ninguém encontrado.</td></tr>'}
</tbody></table></div>`;
return h;
}
function verMil(id){
const u=user(id);const cs=D.cautelas.filter(c=>c.userId===id).sort((a,b)=>String(b.criadoEm).localeCompare(String(a.criadoEm)));
const uso=cs.filter(c=>c.status==='cautelada'||c.status==='separada');
openModal(esc(nomeU(u)),`<dl class="dados-mil"><dt>Nome</dt><dd>${esc(u.nome)}</dd><dt>RG</dt><dd>${esc(u.rg||'—')}</dd><dt>E-mail</dt><dd>${esc(u.email)}</dd><dt>Telefone</dt><dd>${esc(u.telefone||'—')}</dd>
<dt>${u.tipo==='oficial'?'OPM':'Turma'}</dt><dd>${esc(u.tipo==='oficial'?u.opm:[u.turma,turmaU(u)].filter(Boolean).join(' · '))}</dd><dt>Perfil</dt><dd>${u.perfil==='almox'?'Almoxarifado':u.tipo==='oficial'?'Oficial':'Cadete'}</dd></dl>
<div class="sec-h"><h3>Romaneio</h3></div><dl class="dados-mil">${ROM.map(([k,n])=>`<dt>${n}</dt><dd>${esc((u.romaneio||{})[k]||'—')}</dd>`).join('')}</dl>
<div class="sec-h"><h3>Cautelas em aberto</h3><span class="muted small">${uso.length}</span></div>${uso.map(c=>cardCautela(c)).join('')||'<p class="muted small">Nenhuma. Pode emitir o "nada consta".</p>'}
${cs.length>uso.length?`<p class="small muted">${cs.length-uso.length} cautela(s) encerrada(s) no histórico.</p>`:''}`,
`<button class="btn" data-act="nadaConsta" data-id="${id}">${uso.length?'Pendências (PDF)':'Nada consta (PDF)'}</button>
<button class="btn" data-act="editMil" data-id="${id}">Editar dados</button>
${id!==sess.userId?`<button class="btn" data-act="perfilMil" data-id="${id}">${u.perfil==='almox'?'Tirar do almoxarifado':'Tornar almoxarife'}</button>
<button class="btn ${u.ativo?'btn-warn':''}" data-act="ativoMil" data-id="${id}">${u.ativo?'Bloquear acesso':'Liberar acesso'}</button>`:''}`);
}
function editMil(id){
const u=user(id);
openModal('Editar – '+esc(nomeU(u)),`<form id="f-editmil" data-id="${id}" class="stack">${camposDados(u)}<p class="erro" id="em-erro"></p><button class="btn btn-pri btn-block">Salvar</button></form>`);
}
async function salvarMil(form,fd){
const u=user(form.dataset.id);const d=lerDados(fd,u.tipo);
try{await updateDoc(doc(db,'users',u.id),{...d,atualizadoEm:nowISO()});closeModal();toast('Dados salvos.');}catch(e){$('#em-erro').textContent=erroFirebase(e);}
}
/* Cadastro feito pelo almoxarife (oficial de fora da EsFO ou exceções), como o "Cadastrar manualmente" do SICAM.
   O próprio oficial digita a senha: é com ela que ele assina a cautela no balcão. */
function formNovoMil(){
openModal('Cadastrar oficial de fora da EsFO',`<form id="f-novomil" class="stack" autocomplete="off">
<p class="aviso">Faça o cadastro com o oficial presente. Ele mesmo digita a senha no fim: é com ela que vai assinar as cautelas no balcão.</p>
${camposIdent({},'oficial')}
<div class="grid2"><label class="f"><span>RG</span><input class="i" name="rg" required inputmode="numeric"></label><label class="f"><span>OPM / unidade</span><input class="i" name="opm" required placeholder="Ex.: 12º BPM"></label></div>
<label class="f"><span>Telefone (WhatsApp)</span><input class="i" name="telefone" inputmode="tel"></label>
<label class="f"><span>E-mail (de preferência o institucional)</span><input class="i" name="email" type="email" required autocapitalize="off"></label>
<details><summary class="small">Romaneio (opcional)</summary>${camposRom({})}</details>
<div class="grid2"><label class="f"><span>Senha do oficial (mín. 8)</span><input class="i" name="senha" type="password" required minlength="8" autocomplete="new-password"></label>
<label class="f"><span>Repita a senha</span><input class="i" name="senha2" type="password" required minlength="8" autocomplete="new-password"></label></div>
<p class="erro" id="nm-erro"></p><button class="btn btn-pri btn-block">Cadastrar oficial</button></form>`);
}
async function salvarNovoMil(form,fd){
const err=m=>{$('#nm-erro').textContent=m;};
const email=String(fd.get('email')||'').trim().toLowerCase();
if(!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email))return err('E-mail inválido.');
if(fd.get('senha')!==fd.get('senha2'))return err('As senhas não conferem.');
const d=lerDados(fd,'oficial');
let uid;
try{uid=await comAuthSecundario(async a2=>{const c=await createUserWithEmailAndPassword(a2,email,String(fd.get('senha')));try{if(dominioOk(email))await sendEmailVerification(c.user);}catch(e){}return c.user.uid;});}
catch(e){return err(e.code==='auth/email-already-in-use'?'Já existe uma conta com esse e-mail. Procure o oficial na lista de militares.':erroFirebase(e));}
await setDoc(doc(db,'users',uid),{...d,tipo:'oficial',externo:true,email,perfil:'cadete',ativo:true,pendente:false,criadoEm:nowISO(),criadoPor:sess.userId,lgpd:nowISO()});
closeModal();toast(`${d.grad} ${d.guerra} cadastrado. Já pode receber cautela no balcão.`);
}
async function liberar(id){const u=user(id);if(u.perfil==='almox'&&!confirm(`${nomeU(u)} pediu conta do ALMOXARIFADO: vai poder separar, entregar, receber devoluções e mexer no estoque. Liberar?`))return;await updateDoc(doc(db,'users',id),{ativo:true,pendente:false,liberadoPor:sess.userId,liberadoEm:nowISO()});toast('Acesso liberado.');}
async function negarCad(id){if(!confirm('Recusar este cadastro?'))return;await updateDoc(doc(db,'users',id),{ativo:false,pendente:false,recusadoPor:sess.userId,recusadoEm:nowISO()});toast('Cadastro recusado.');}
async function ativoMil(id){const u=user(id);if(u.ativo&&!confirm(`Bloquear o acesso de ${nomeU(u)}? O material em nome dele continua registrado.`))return;
await updateDoc(doc(db,'users',id),{ativo:!u.ativo,pendente:false});closeModal();toast(u.ativo?'Acesso bloqueado.':'Acesso liberado.');}
async function perfilMil(id){const u=user(id);const novo=u.perfil==='almox'?'cadete':'almox';
if(!confirm(novo==='almox'?`${nomeU(u)} vai poder separar, entregar, receber devolução e mexer no estoque. Confirmar?`:`Tirar ${nomeU(u)} do almoxarifado?`))return;
await updateDoc(doc(db,'users',id),{perfil:novo});closeModal();toast('Perfil alterado.');}
/* Diretório resumido: só o necessário para escolher o destino de uma transferência (sem RG, telefone ou romaneio) */
let dirUltimo='';
async function publicarDiretorio(){
if(!ehAlmox())return;
const lista=D.users.filter(u=>u.ativo).map(u=>({id:u.id,grad:u.grad||'',guerra:u.guerra||'',nome:u.nome||'',tipo:u.tipo||'cadete',ano:u.ano||'',pelotao:u.pelotao||'',opm:u.opm||''}))
.sort((a,b)=>a.id.localeCompare(b.id));
const j=JSON.stringify(lista);if(j===dirUltimo)return;
const atual=JSON.stringify(((D.dirDoc||{}).lista)||[]);if(j===atual){dirUltimo=j;return;}
try{await setDoc(doc(db,'config','diretorio'),{lista,em:nowISO()});dirUltimo=j;}catch(e){console.warn('diretório',e);}
}

/* ============ Histórico ============ */
function vHist(){
const q=norm(ui.hq);const fonte=ui.histTudo?baldes.tudo:D.cautelas;
let l=fonte.filter(c=>!q||norm(nomeM(c.userId)+' '+itensTxt(c)+' '+c.num+' '+(ST[c.status]||[''])[0]).includes(q)).sort((a,b)=>String(b.atualizadoEm||b.criadoEm).localeCompare(String(a.atualizadoEm||a.criadoEm)));
return `<div class="a-head"><div><h1>Histórico</h1><p>${ui.histTudo?'Todas as cautelas':'Cautelas abertas e as movimentadas nos últimos '+HIST_DIAS+' dias'}</p></div>
<div class="row">${ui.histTudo?'':'<button class="btn" data-act="histTudo">Carregar tudo</button>'}<button class="btn" data-act="csvHist">Exportar (CSV)</button><button class="btn" data-act="backup">Backup completo (JSON)</button></div></div>
<div class="filters"><input class="i" data-inp="hq" placeholder="Buscar" value="${esc(ui.hq)}"></div>
<div class="tbl-wrap"><table><thead><tr><th>Nº</th><th>Militar</th><th>Material</th><th>Situação</th><th>Atualizado</th></tr></thead><tbody>
${l.slice(0,400).map(c=>`<tr class="hov" data-act="ver" data-id="${c.id}"><td class="mono">${nr(c.num)}</td><td>${esc(nomeM(c.userId))}</td><td>${esc(itensTxt(c))}</td><td>${stamp(c)}</td><td>${fmt(c.atualizadoEm||c.criadoEm)}</td></tr>`).join('')||'<tr><td colspan="5" class="muted">Nada encontrado.</td></tr>'}
</tbody></table></div>`;
}
async function carregarHistTudo(){
try{const s=await getDocs(collection(db,'cautelas'));baldes.tudo=s.docs.map(d=>({id:d.id,...d.data()}));ui.histTudo=true;
baldes.tudo.forEach(c=>{if(!D.cautelas.some(x=>x.id===c.id))D.cautelas.push(c);});render();}catch(e){toast(erroFirebase(e),true);}
}

/* ============ Planilhas, backup e impressões ============ */
function baixar(nome,conteudo,tipo){const b=new Blob([conteudo],{type:tipo});const a=document.createElement('a');a.href=URL.createObjectURL(b);a.download=nome;document.body.appendChild(a);a.click();setTimeout(()=>{URL.revokeObjectURL(a.href);a.remove();},500);}
const csvCel=v=>{const s=String(v==null?'':v);return /[;"\n]/.test(s)?'"'+s.replace(/"/g,'""')+'"':s;};
const csv=linhas=>'﻿'+linhas.map(l=>l.map(csvCel).join(';')).join('\n');
const hoje=()=>new Date().toISOString().slice(0,10);
function csvUso(){
const l=[['Nº','Militar','Nome completo','Turma/OPM','Item','Tamanho','Qtd em uso','Desde','Prazo','Em atraso']];
ativasA().forEach(c=>{const u=user(c.userId);pendentes(c).forEach(x=>l.push([c.num,nomeU(u),u.nome,turmaU(u),x.nome,x.tam,pend(x),fmtD(c.entregueEm||c.criadoEm),c.prazo?fmtD(c.prazo):'',atrasada(c)?'SIM':'']));});
baixar(`almox-esfo-em-uso-${hoje()}.csv`,csv(l),'text/csv;charset=utf-8');
}
function csvHist(){
const l=[['Nº','Militar','Situação','Origem','Item','Tamanho','Qtd','Devolvido','Transferido','Criada','Atualizada','Prazo']];
(ui.histTudo?baldes.tudo:D.cautelas).forEach(c=>(c.itens||[]).forEach(x=>l.push([c.num,nomeM(c.userId),(ST[c.status]||[c.status])[0],c.origem,x.nome,x.tam,x.qtd,x.dev||0,x.trf||0,fmt(c.criadoEm),fmt(c.atualizadoEm),c.prazo?fmtD(c.prazo):''])));
baixar(`almox-esfo-historico-${hoje()}.csv`,csv(l),'text/csv;charset=utf-8');
}
function csvMil(){
const l=[['Graduação/posto','Nome de guerra','Nome completo','RG','Tipo','Ano','Pelotão','Turma','OPM','E-mail','Telefone',...ROM.map(r=>r[1]),'Situação']];
D.users.forEach(u=>l.push([u.grad,u.guerra,u.nome,u.rg,u.tipo,u.ano,u.pelotao,u.turma,u.opm,u.email,u.telefone,...ROM.map(([k])=>(u.romaneio||{})[k]||''),u.ativo?'Ativo':u.pendente?'Pendente':'Sem acesso']));
baixar(`almox-esfo-militares-${hoje()}.csv`,csv(l),'text/csv;charset=utf-8');
}
async function backup(){
try{const out={versao:VERSAO,em:nowISO()};
for(const col of ['users','categorias','itens','cautelas','movimentos']){const s=await getDocs(collection(db,col));out[col]=s.docs.map(d=>({id:d.id,...d.data()}));}
baixar(`almox-esfo-backup-${hoje()}.json`,JSON.stringify(out,null,1),'application/json');toast('Backup baixado. Guarde em local seguro.');}catch(e){toast(erroFirebase(e),true);}
}
function janelaImpressao(titulo,corpo){
const w=window.open('','_blank');if(!w){toast('Permita a abertura de janelas para imprimir.',true);return;}
const base=location.href.replace(/[#?].*$/,'').replace(/[^/]*$/,'');
w.document.write(`<!doctype html><html lang="pt-BR"><head><meta charset="utf-8"><title>${esc(titulo)}</title><base href="${base}">
<style>body{font:13px/1.45 Arial,sans-serif;color:#111;margin:24px}header{display:flex;align-items:center;gap:14px;border-bottom:3px solid #003478;padding-bottom:10px;margin-bottom:16px}
header img{height:70px}header h1{font-size:17px;margin:0}header p{margin:2px 0 0;font-size:12px}h2{font-size:15px;text-align:center;margin:12px 0}
table{width:100%;border-collapse:collapse;margin:10px 0}th,td{border:1px solid #999;padding:5px 7px;text-align:left}th{background:#eef2f8}
.ass{border:1px solid #003478;padding:8px 10px;margin-top:12px;font-size:11px;word-break:break-all}.dec{margin:12px 0;text-align:justify}footer{margin-top:24px;font-size:10px;color:#555}
@media print{button{display:none}}</style></head><body>
<header><img src="brasao-apmg.png"><div><h1>POLÍCIA MILITAR DO PARANÁ<br>ACADEMIA POLICIAL MILITAR DO GUATUPÊ<br>ESCOLA DE FORMAÇÃO DE OFICIAIS – ALMOXARIFADO</h1></div><img src="brasao-esfo.png" style="margin-left:auto"></header>
${corpo}<footer>Documento gerado pelo ${NOME} v${VERSAO} em ${fmt(nowISO())} por ${esc(nomeM(sess.userId))}.</footer>
<p><button onclick="print()">Imprimir</button></p><script>setTimeout(()=>print(),600)<\/script></body></html>`);
w.document.close();
}
function termo(id){
const c=C(id);if(!c)return;const u=user(c.userId);const a=c.assinatura||{};
janelaImpressao('Termo de cautela '+nr(c.num),`<h2>TERMO DE CAUTELA ${nr(c.num)}</h2>
<table><tr><th>Militar</th><td>${esc(nomeU(u))} – ${esc(u.nome||'')}</td><th>RG</th><td>${esc(u.rg||'')}</td></tr><tr><th>${u.tipo==='oficial'?'OPM':'Turma'}</th><td>${esc(u.tipo==='oficial'?u.opm:[u.turma,turmaU(u)].filter(Boolean).join(' · '))}</td><th>Prazo</th><td>${c.prazo?fmtD(c.prazo):'Sem prazo definido'}</td></tr></table>
<table><thead><tr><th>Item</th><th>Tamanho</th><th>Qtd</th><th>Devolvido</th><th>Transferido</th></tr></thead><tbody>${(c.itens||[]).map(x=>`<tr><td>${esc(x.nome)}${x.consumo?' (entrega definitiva)':''}</td><td>${esc(x.tam)}</td><td>${x.qtd}</td><td>${x.dev||0}</td><td>${x.trf||0}</td></tr>`).join('')}</tbody></table>
<p class="dec">Declaro que recebi do Almoxarifado da Escola de Formação de Oficiais o material acima relacionado, em perfeitas condições de uso, comprometendo-me a zelar por sua guarda e conservação e a devolvê-lo ${c.prazo?'até '+fmtD(c.prazo):'quando solicitado'}, ciente de que responderei pelo extravio ou dano causado por mau uso.</p>
<div class="ass"><b>Assinatura eletrônica:</b> ${esc(nomeM(a.por||c.userId))} em ${fmt(a.em)} – ${esc(FORMA[a.metodo]||a.metodo||'')}<br><b>Código de conferência (SHA-256):</b> ${esc(a.hash||'')}<br><b>Texto assinado:</b> ${esc(a.dados||'')}</div>
${(c.log||[]).length?`<table><thead><tr><th>Data</th><th>Evento</th><th>Por</th><th>Obs.</th></tr></thead><tbody>${c.log.map(x=>`<tr><td>${fmt(x.t)}</td><td>${esc(x.a)}</td><td>${esc(nomeM(x.por))}</td><td>${esc(x.obs||'')}</td></tr>`).join('')}</tbody></table>`:''}`);
}
function nadaConsta(id){
const u=user(id);const uso=D.cautelas.filter(c=>c.userId===id&&(c.status==='cautelada'||c.status==='separada'));
const ident=`<table><tr><th>Militar</th><td>${esc(nomeU(u))} – ${esc(u.nome||'')}</td><th>RG</th><td>${esc(u.rg||'')}</td></tr><tr><th>${u.tipo==='oficial'?'OPM':'Turma'}</th><td colspan="3">${esc(u.tipo==='oficial'?u.opm:[u.turma,turmaU(u)].filter(Boolean).join(' · '))}</td></tr></table>`;
if(!uso.length)janelaImpressao('Nada consta',`<h2>DECLARAÇÃO DE NADA CONSTA</h2>${ident}<p class="dec">Declaro, para os devidos fins, que <b>NADA CONSTA</b> em nome do militar acima identificado no Almoxarifado da Escola de Formação de Oficiais, não havendo material cautelado pendente de devolução até a presente data.</p>
<p style="margin-top:50px;text-align:center">_____________________________________<br>${esc(nomeM(sess.userId))}<br>Responsável pelo Almoxarifado – EsFO</p>`);
else janelaImpressao('Pendências',`<h2>MATERIAL PENDENTE DE DEVOLUÇÃO</h2>${ident}<table><thead><tr><th>Nº</th><th>Item</th><th>Tam.</th><th>Qtd</th><th>Prazo</th></tr></thead><tbody>${uso.map(c=>(c.status==='separada'?c.itens:pendentes(c)).map(x=>`<tr><td>${nr(c.num)}</td><td>${esc(x.nome)}</td><td>${esc(x.tam)}</td><td>${c.status==='separada'?x.qtd:pend(x)}</td><td>${c.prazo?fmtD(c.prazo):'—'}</td></tr>`).join('')).join('')}</tbody></table>`);
}

/* ============ Catálogo inicial (carregado uma vez, com estoque zerado) ============ */
const CATALOGO=[
['Uniforme de desfile',[['Túnica branca do uniforme especial de desfile','un','gandola','P,M,G,GG,XG'],['Túnica cinza do uniforme especial de desfile','un','gandola','P,M,G,GG,XG'],['Calça do uniforme especial de desfile','un','calca','36,38,40,42,44,46,48,50,52']]],
['Coberturas',[['Barretina','un','cobertura','54,55,56,57,58,59,60,61,62'],['Penacho','un','','Único']]],
['Luvas',[['Luva branca','par','luva','P,M,G,GG'],['Luva de couro','par','luva','P,M,G,GG']]],
['Calçados',[['Sapato social','par','calcado','37,38,39,40,41,42,43,44,45,46'],['Polainas','par','','Único']]],
['Insígnias e distintivos',[['Platina – 1º ano','par','','Único'],['Platina – 2º ano','par','','Único'],['Platina – 3º ano','par','','Único'],['Losango','un','','Único'],['Dragoneira','un','','Único']]],
['Acessórios',[['Forragê','un','','Único'],['Cinto','un','cinto','P,M,G,GG'],['Bucaneiras','par','','Único'],['Guia de espada','un','','Único'],['Gancho','un','','Único'],['Manicaca','un','','Único']]]
];
let semeando=false;
async function semearCatalogo(){
if(semeando||!D.setup||!D.setup.seed||D.setup.seeded)return;semeando=true;
try{const b=writeBatch(db);
CATALOGO.forEach(([cn,its],ci)=>{const cid='cat'+(ci+1);b.set(doc(db,'categorias',cid),{nome:cn,ordem:(ci+1)*10,icone:['uniforme','cobertura','luvas','calcados','insignias','correame'][ci]||'generico'});
its.forEach(([n,un,campo,tams],ii)=>{const t=tams.split(',').map(s=>s.trim());const e={};t.forEach(x=>e[x]={total:0,disp:0});
b.set(doc(collection(db,'itens')),{catId:cid,nome:n,unidade:un,campo,tamanhos:t,estoque:e,consumo:false,ativo:true,ordem:ii*10});});});
b.update(doc(db,'config','setup'),{seeded:true});await b.commit();toast('Catálogo inicial carregado. Registre as entradas de estoque em "Material".');}
catch(e){console.error(e);semeando=false;}
}

/* ============ Ajustes do catálogo inicial (rodam uma vez, no painel do almoxarifado) ============ */
let migrando=false;
async function migrarCatalogo(){
const feitas=(D.setup&&D.setup.migr)||[];if(migrando||!D.setup||!D.setup.seeded||feitas.includes('v14'))return;migrando=true;
try{const b=writeBatch(db);let n=0;
// "Correame e acessórios" passa a ser só "Acessórios"
let acess=D.cats.find(c=>norm(c.nome)==='correame e acessorios')||D.cats.find(c=>norm(c.nome)==='acessorios');
if(acess&&norm(acess.nome)!=='acessorios'){b.update(doc(db,'categorias',acess.id),{nome:'Acessórios',icone:'correame'});n++;}
// Forragê é cordão de ombro da túnica: sai de Coberturas e vai para Acessórios, tamanho único
const forr=D.itens.find(i=>norm(i.nome)==='forrage');
if(forr&&acess&&forr.catId!==acess.id){const semEstoque=(forr.tamanhos||[]).every(t=>!est(forr,t).total);
b.update(doc(db,'itens',forr.id),{catId:acess.id,nome:'Forragê',campo:'',...(semEstoque?{tamanhos:['Único'],estoque:{'Único':{total:0,disp:0}}}:{})});n++;}
// Túnica do especial de desfile: branca e cinza
const tun=D.itens.find(i=>norm(i.nome)==='tunica do uniforme especial de desfile');
if(tun){b.update(doc(db,'itens',tun.id),{nome:'Túnica branca do uniforme especial de desfile'});n++;
if(!D.itens.some(i=>norm(i.nome).startsWith('tunica cinza'))){const e={};(tun.tamanhos||[]).forEach(t=>e[t]={total:0,disp:0});
b.set(doc(collection(db,'itens')),{catId:tun.catId,nome:'Túnica cinza do uniforme especial de desfile',unidade:tun.unidade||'un',campo:tun.campo||'gandola',tamanhos:tun.tamanhos||['Único'],estoque:e,consumo:false,ativo:true,ordem:(tun.ordem||0)+5});n++;}}
b.update(doc(db,'config','setup'),{migr:[...feitas,'v14']});await b.commit();
if(n)toast('Catálogo ajustado: túnica branca e cinza, forragê em Acessórios.');}
catch(e){console.error(e);migrando=false;}
}

/* ============ Eventos ============ */
const acts={
go:el=>{ui.view=el.dataset.v;closeModal();render();window.scrollTo(0,0);},
fechar:closeModal,
recarregar:()=>location.reload(),
sair:async()=>{closeModal();ui.view=null;ui.cart=[];await signOut(auth);},
tema:el=>{temaAtual=el.dataset.tema;try{localStorage.setItem('almox.tema',temaAtual);}catch(e){}aplicarTema(temaAtual);$$('.tema-sel button').forEach(b=>b.setAttribute('aria-pressed',b.dataset.tema===temaAtual));},
irCadastro:el=>{loginMsg='';ui.cadPerfil=el.dataset.p||'cadete';fase='cadastro';render();},
tela:el=>{ui.tela=el.dataset.t;loginMsg='';fase='login';render();},
irLogin:()=>{fase='login';render();},
cadTipo:el=>{ui.cadTipo=el.dataset.t;render();},
esqueci:()=>openModal('Esqueci minha senha',`<form id="f-esq" class="stack"><label class="f"><span>E-mail institucional</span><input class="i" name="email" type="text" required autocapitalize="off"></label>
<p class="erro" id="esq-erro"></p><button class="btn btn-pri btn-block">Enviar link para nova senha</button></form>`),
jaConfirmei:async()=>{const u=auth.currentUser;if(!u)return;await u.reload();if(auth.currentUser.emailVerified){await auth.currentUser.getIdToken(true);await aoMudarLogin(auth.currentUser);}else $('#ver-erro').textContent='Ainda não consta a confirmação. Clique no link do e-mail e tente de novo.';},
reenviar:async()=>{try{await sendEmailVerification(auth.currentUser);toast('E-mail reenviado.');}catch(e){toast(e.code==='auth/too-many-requests'?'Aguarde alguns minutos antes de reenviar.':erroFirebase(e),true);}},
senha:trocarSenha,
ativarBio:ativarBio,
ativarBioAqui:async()=>{const p=assPend;await ativarBio();if(p&&temBioAqui())pedirAssinatura(p);},
assBio:()=>assinarComBio(),
// cadete
cat:el=>{ui.cat=el.dataset.id;render();},
tam:el=>{ui.tamSel=ui.tamSel||{};ui.tamSel[el.dataset.id]=el.dataset.t;render();},
addCart:el=>addCart(el.dataset.id),
abrirPedido:abrirPedido,
cartQ:el=>{const x=ui.cart[+el.dataset.i];if(!x)return;x.qtd=Math.max(0,Math.min(5,x.qtd+(+el.dataset.d)));if(!x.qtd)ui.cart.splice(+el.dataset.i,1);if(ui.cart.length)abrirPedido();else closeModal();},
cartRm:el=>{ui.cart.splice(+el.dataset.i,1);if(ui.cart.length)abrirPedido();else closeModal();},
limparCart:()=>{ui.cart=[];closeModal();},
enviarPedido:enviarPedido,
ver:el=>verCautela(el.dataset.id),
cancelarPedido:el=>{if(confirm('Cancelar este pedido?'))cancelarPedido(el.dataset.id);},
assinar:el=>assinar(el.dataset.id),
transferir:el=>transferir(el.dataset.id),
desistirTrf:el=>desistirTrf(el.dataset.id),
aceitarTrf:el=>aceitarTrf(el.dataset.id),
recusarTrf:el=>{if(confirm('Recusar esta transferência?'))recusarTrf(el.dataset.id);},
termo:el=>termoPDF(el.dataset.id),
// almoxarifado
separar:el=>separar(el.dataset.id),
confirmarSep:el=>confirmarSep(el.dataset.id),
recusar:el=>recusar(el.dataset.id),
cancelarSep:el=>cancelarSep(el.dataset.id),
entregar:el=>entregar(el.dataset.id),
assBalcao:el=>assBalcao(el.dataset.id),
balcao:()=>abrirBalcao(),
balAdd:balAdd,
balRm:el=>{ui.bal.linhas.splice(+el.dataset.i,1);desenharBalcao();},
balGravar:balGravar,
devolver:el=>devolver(el.dataset.id),
confirmarDev:el=>confirmarDev(el.dataset.id),
prazo:el=>editarPrazo(el.dataset.id),
novaCat:()=>formCat(null),
editCat:el=>formCat(D.cats.find(c=>c.id===el.dataset.id)),
novoItem:el=>{if(!D.cats.length){toast('Crie uma categoria primeiro.',true);return;}formItem(null,el.dataset.cat||ui.matCat||'');},
matCat:el=>{ui.matCat=el.dataset.id||null;ui.matQ='';render();window.scrollTo(0,0);},
catSol:el=>{ui.cat=el.dataset.id||null;render();window.scrollTo(0,0);},
editItem:el=>formItem(item(el.dataset.id)),
entrada:el=>formEntrada(el.dataset.id),
ajuste:el=>{ui.ajModo='baixa';formAjuste(el.dataset.id);},
ajModo:el=>{ui.ajModo=el.dataset.m;formAjuste($('#f-aj').dataset.id);},
quem:el=>quemEsta(el.dataset.id),
liberar:el=>liberar(el.dataset.id),
novoMil:()=>formNovoMil(),
negarCad:el=>negarCad(el.dataset.id),
verMil:el=>verMil(el.dataset.id),
editMil:el=>editMil(el.dataset.id),
ativoMil:el=>ativoMil(el.dataset.id),
perfilMil:el=>perfilMil(el.dataset.id),
nadaConsta:el=>nadaConstaPDF(el.dataset.id),
importar:()=>abrirImportar(),
modeloImp:()=>baixarModelo(),
impModo:el=>{ui.impModo=el.dataset.m;$$('#f-imp .seg button').forEach(b=>b.setAttribute('aria-pressed',b.dataset.m===ui.impModo));if(ui.imp)desenharPreviaImp();},
confirmarImp:()=>confirmarImp(),
histTudo:carregarHistTudo,
csvUso:csvUso,csvHist:csvHist,csvMil:csvMil,backup:backup
};
document.addEventListener('click',e=>{
const el=e.target.closest('[data-act]');if(!el)return;
const f=acts[el.dataset.act];if(!f)return;
if(el.tagName==='A')e.preventDefault();
Promise.resolve().then(()=>f(el)).catch(err=>{console.error(err);toast(erroFirebase(err),true);});
});
const forms={
'f-login':(f,fd)=>fazerLogin(fd),
'f-cad':(f,fd)=>fazerCadastro(f,fd,false),
'f-setup':(f,fd)=>fazerCadastro(f,fd,true),
'f-esq':async(f,fd)=>{if(!String(fd.get('email')).includes('@')){$('#esq-erro').textContent='Contas por usuário não recebem e-mail: peça ao responsável pelo almoxarifado para criar uma nova.';return;}try{await sendPasswordResetEmail(auth,String(fd.get('email')).trim().toLowerCase());closeModal();toast('Se o e-mail estiver cadastrado, o link para nova senha foi enviado.');}catch(e){$('#esq-erro').textContent=erroFirebase(e);}},
'f-senha':(f,fd)=>salvarSenha(fd),
'f-perfil':(f,fd)=>salvarPerfil(fd),
'f-ass':(f,fd)=>assinarComSenha(fd),
'f-trf':(f,fd)=>confirmarTransf(f,fd),
'f-recusar':(f,fd)=>confirmarRecusa(f,fd),
'f-assbal':(f,fd)=>confirmarAssBalcao(f,fd),
'f-prazo':(f,fd)=>salvarPrazo(f,fd),
'f-cat':(f,fd)=>salvarCat(f,fd),
'f-item':(f,fd)=>salvarItem(f,fd),
'f-ent':(f,fd)=>salvarEntrada(f,fd),
'f-aj':(f,fd)=>salvarAjuste(f,fd),
'f-editmil':(f,fd)=>salvarMil(f,fd),
'f-novomil':(f,fd)=>salvarNovoMil(f,fd),
'f-pedido':()=>enviarPedido(),
'f-bal':()=>balAdd()
};
document.addEventListener('submit',e=>{
const f=e.target;const h=forms[f.id]||(f.dataset&&f.dataset.rel?gerarRelatorio:null);if(!h)return;e.preventDefault();
const btn=f.querySelector('button:not([type=button])');if(btn&&btn.disabled)return;
if(btn&&f.id!=='f-cad'&&f.id!=='f-setup')btn.disabled=true;
Promise.resolve().then(()=>h(f,new FormData(f))).catch(err=>{console.error(err);toast(erroFirebase(err),true);}).finally(()=>{if(btn&&document.body.contains(btn))btn.disabled=false;});
});
document.addEventListener('input',e=>{
const k=e.target.dataset&&e.target.dataset.inp;if(!k)return;
if(k==='trfq'){filtrarTrf(e.target.value);return;}
ui[k]=e.target.value;render();
});
document.addEventListener('change',e=>{
if(e.target.dataset&&e.target.dataset.chgimp){const f=e.target.files&&e.target.files[0];if(f)lerImportacao(f);return;}
const k=e.target.dataset&&e.target.dataset.chg;if(!k||!ui.bal)return;
if(k==='balMil'){ui.bal.userId=e.target.value;desenharBalcao();}
if(k==='balIt'){ui.bal.it=e.target.value;desenharBalcao();}
if(k==='balPrazo')ui.bal.prazo=e.target.value;
if(k==='balObs')ui.bal.obs=e.target.value;
});

/* ============ Firebase: sessão e dados ao vivo ============ */
function pararEscutas(){unsubs.forEach(u=>{try{u();}catch(e){}});unsubs=[];loaded={};}
const prevSt=new Map();
function avisosCautelas(snap,admin){
snap.docChanges().forEach(ch=>{const c={id:ch.doc.id,...ch.doc.data()};const ant=prevSt.get(c.id);prevSt.set(c.id,c.status+'|'+(c.assinatura?1:0));
if(ch.type==='removed'||ant===c.status+'|'+(c.assinatura?1:0))return;
if(admin){if(c.status==='solicitada'&&!ant)avisar('Novo pedido',`${nomeM(c.userId)} – ${itensTxt(c)}`);
if(c.status==='separada'&&c.assinatura&&ant&&ant.endsWith('|0'))avisar('Recebimento assinado',`${nomeM(c.userId)} – ${nr(c.num)}. Confirme a entrega.`);}
else if(ant){if(c.status==='separada'&&!c.assinatura)avisar('Material separado',`${nr(c.num)} pronto para retirada. Assine ao receber.`);
if(c.status==='recusada')avisar('Pedido recusado',nr(c.num));
if(c.status==='devolvida')avisar('Devolução registrada',nr(c.num));}
});
}
function juntarCautelas(){const m=new Map();[...baldes.recentes,...baldes.ativas,...baldes.minhas].forEach(c=>m.set(c.id,c));return [...m.values()];}
function escutar(perfil){
const adm=perfil==='almox',uid=sess.userId;prevSt.clear();baldes.ativas=[];baldes.recentes=[];baldes.minhas=[];baldes.tudo=[];ui.histTudo=false;dirUltimo='';
const corte=new Date(Date.now()-HIST_DIAS*864e5).toISOString();
const fontes=adm?[['users',collection(db,'users')],['cats',collection(db,'categorias')],['itens',collection(db,'itens')],
['ativas',query(collection(db,'cautelas'),where('status','in',['solicitada','separada','cautelada']))],['recentes',query(collection(db,'cautelas'),where('atualizadoEm','>=',corte))],
['setup',doc(db,'config','setup')],['dir',doc(db,'config','diretorio')]]
:[['eu',doc(db,'users',uid)],['cats',collection(db,'categorias')],['itens',collection(db,'itens')],['minhas',query(collection(db,'cautelas'),where('userId','==',uid))],
['trfIn',query(collection(db,'cautelas'),where('transferPara','==',uid))],['dir',doc(db,'config','diretorio')]];
const nomes=fontes.map(f=>f[0]);
fontes.forEach(([nome,ref])=>{
const pronto=()=>{if(loaded[nome])return;loaded[nome]=true;if(nomes.every(n=>loaded[n])){fase='app';render();if(adm){publicarDiretorio();semearCatalogo();migrarCatalogo();}}};
const depois=prim=>{if(prim)pronto();else if(fase==='app'){if(!modal.open)render();if(adm){publicarDiretorio();semearCatalogo();migrarCatalogo();}}};
const falha=err=>{console.error(nome,err);if(err.code==='permission-denied'&&(nome==='eu'||nome==='users')){loginMsg='Sem permissão de acesso. Procure o almoxarifado.';signOut(auth);return;}
if(nome==='dir'||nome==='trfIn'||nome==='setup'){pronto();return;}toast(erroFirebase(err),true);pronto();};
if(ref.type==='document'){
unsubs.push(onSnapshot(ref,sn=>{const prim=!loaded[nome];const d=sn.exists()?{id:sn.id,...sn.data()}:null;
if(nome==='eu'){D.eu=d;if(!d||!d.ativo){loginMsg='Seu acesso foi bloqueado. Procure o almoxarifado.';signOut(auth);return;}D.users=[d];}
if(nome==='setup')D.setup=d;
if(nome==='dir'){D.dirDoc=d;D.dir=(d&&d.lista)||[];}
depois(prim);},falha));
return;}
unsubs.push(onSnapshot(ref,snap=>{const prim=!loaded[nome];
let arr=snap.docs.map(d=>({id:d.id,...d.data()}));
if(nome==='users'){if(!prim)snap.docChanges().forEach(ch=>{const u=ch.doc.data();if(u.pendente&&ch.type==='added')avisar('Novo cadastro para liberar',`${u.grad||''} ${u.guerra||''} – ${u.pelotao||u.opm||''}`);});
D.users=arr;const eu=D.users.find(u=>u.id===uid);if(!eu||!eu.ativo||eu.perfil!=='almox'){if(eu&&eu.ativo){aoMudarLogin(auth.currentUser);return;}loginMsg='Seu acesso foi bloqueado.';signOut(auth);return;}}
else if(nome==='cats')D.cats=ordenarCats(arr);
else if(nome==='itens'){D.itens=arr;ordenarItens(D.itens);}
else if(nome==='trfIn'){if(!prim)snap.docChanges().forEach(ch=>{if(ch.type==='added'){const c=ch.doc.data();avisar('Transferência para você',`${nomeM(c.userId)} quer transferir material. Abra o Início para aceitar.`);}});D.trfIn=arr;}
else{if(prim)snap.docs.forEach(d=>prevSt.set(d.id,d.data().status+'|'+(d.data().assinatura?1:0)));else avisosCautelas(snap,adm);
baldes[nome]=arr;D.cautelas=juntarCautelas();if(ui.histTudo)D.cautelas=[...new Map([...baldes.tudo,...D.cautelas].map(c=>[c.id,c])).values()];}
depois(prim);
},err=>{
if(nome==='trfIn'||nome==='recentes'){console.warn(nome,err);baldes[nome]=[];pronto();return;}
falha(err);}));
});
}
async function setupFeito(){try{const s=await getDoc(doc(db,'config','setup'));return s.exists();}catch(e){return true;}}
async function aoMudarLogin(u){
if(bootstrapping)return;
pararEscutas();closeModal();if(aguardandoUnsub){aguardandoUnsub();aguardandoUnsub=null;}
try{
if(!u){sess=null;D=D0();const f=(await setupFeito())?'login':'setup';fase=(fase==='cadastro'&&f==='login')?fase:f;render();return;}
if(!u.emailVerified&&!ehFicticio(u.email)){fase='verificar';render();return;}
fase='carregando';render();
const s=await getDoc(doc(db,'users',u.uid));
if(!s.exists()){loginMsg='Não há cadastro seu no Almox EsFO. Toque em "Criar minha conta".';await signOut(auth);return;}
const x=s.data();
if(x.pendente){fase='aguardando';render();
aguardandoUnsub=onSnapshot(doc(db,'users',u.uid),d=>{const y=d.data();if(y&&y.ativo){aguardandoUnsub&&aguardandoUnsub();aguardandoUnsub=null;aoMudarLogin(auth.currentUser);}
else if(y&&!y.pendente&&!y.ativo){loginMsg='Seu cadastro não foi liberado. Procure o almoxarifado.';signOut(auth);}},()=>{});
return;}
if(!x.ativo){loginMsg='Seu acesso está bloqueado. Procure o almoxarifado.';await signOut(auth);return;}
if(ui.telaLogin==='almox'&&x.perfil!=='almox'){ui.telaLogin=null;loginMsg='Esta conta não é do almoxarifado. Use o acesso dos cadetes.';await signOut(auth);return;}
ui.telaLogin=null;
sess={userId:u.uid};D=D0();D.eu={id:u.uid,...x};D.users=[D.eu];ui.view=null;
escutar(x.perfil);
}catch(e){console.error(e);erroMsg=erroFirebase(e);fase='erro';render();}
}

/* ============ Render ============ */
function render(){
const ae=document.activeElement,keep=ae&&ae.dataset&&ae.dataset.inp,pos=keep?ae.selectionStart:0;
let html;
if(fase==='naoconfig')html=vNaoConfig();
else if(fase==='erro')html=vErro();
else if(fase==='carregando')html=vCarregando();
else if(fase==='setup')html=vSetup();
else if(fase==='cadastro')html=vCadastro();
else if(fase==='verificar')html=vVerificar();
else if(fase==='aguardando')html=vAguardando();
else if(fase==='login'||!sess||!me())html=fase==='app'?vCarregando():vLogin();
else html=ehAlmox()?vAdmin():vApp();
$('#app').innerHTML=html;
document.title=sess&&fase==='app'?`${NOME}${ehAlmox()&&solicitadas().length?' ('+solicitadas().length+')':''}`:`${NOME} – Cautela de Materiais`;
if(keep){const el=document.querySelector(`[data-inp="${keep}"]`);if(el){el.focus();try{el.setSelectionRange(pos,pos);}catch(e){}}}
}
render();
if(configurado){
try{
app=initializeApp(FB);auth=getAuth(app);try{auth.useDeviceLanguage();}catch(e){}
const ehSafari=/iP(hone|ad|od)/.test(navigator.userAgent)||(navigator.platform==='MacIntel'&&navigator.maxTouchPoints>1)||(/Safari\//.test(navigator.userAgent)&&!/Chrome|Chromium|Android/.test(navigator.userAgent));
try{db=ehSafari?initializeFirestore(app,{experimentalForceLongPolling:true}):getFirestore(app);}catch(e){db=getFirestore(app);}
onAuthStateChanged(auth,aoMudarLogin);
}catch(e){erroMsg=erroFirebase(e);fase='erro';render();}
}
setInterval(()=>{if(fase==='app'&&!modal.open&&!(document.activeElement&&document.activeElement.matches('input,select,textarea')))render();},60000);
if('serviceWorker' in navigator)navigator.serviceWorker.register('sw.js').catch(()=>{});

/* ============ Relatórios em PDF (mesmo visual do SICAM: faixa azul com o brasão, rodapé com páginas) ============ */
async function carregarPDFLib(){
if(window.PDFLib)return window.PDFLib;
for(const src of ['https://cdnjs.cloudflare.com/ajax/libs/pdf-lib/1.17.1/pdf-lib.min.js','https://cdn.jsdelivr.net/npm/pdf-lib@1.17.1/dist/pdf-lib.min.js']){
try{await new Promise((res,rej)=>{const sc=document.createElement('script');sc.src=src;sc.onload=res;sc.onerror=rej;document.head.appendChild(sc);});if(window.PDFLib)return window.PDFLib;}catch(e){}
}
throw {msg:'Não foi possível carregar o gerador de PDF. Confira a internet e tente de novo.'};
}
const winAnsi=s=>String(s==null?'':s).replace(/[“”]/g,'"').replace(/[‘’]/g,"'").replace(/→/g,'->').replace(/✓/g,'OK').replace(/ | /g,' ').replace(/[^\n\x20-\x7E -ÿ–—•€]/g,'');
let brasaoBytes=null;
async function brasaoPDF(pdf){try{if(!brasaoBytes){const r=await fetch('brasao-esfo.png');if(!r.ok)throw new Error('brasão');brasaoBytes=await r.arrayBuffer();}return await pdf.embedPng(brasaoBytes);}catch(e){console.warn('brasão no PDF',e);return null;}}
const carimboArq=()=>{const d=new Date(),p=n=>String(n).padStart(2,'0');return `${d.getFullYear()}${p(d.getMonth()+1)}${p(d.getDate())}-${p(d.getHours())}${p(d.getMinutes())}`;};
/* Monta o PDF: desenhar(ctx) recebe as ferramentas de escrita (texto, kv, tabela, secao) */
async function gerarPDF(titulo,sub,arq,desenhar,paisagem){
const P=await carregarPDFLib();const pdf=await P.PDFDocument.create();
pdf.setTitle(winAnsi(NOME+' – '+titulo));pdf.setAuthor(winAnsi(nomeM(sess.userId)));pdf.setCreator('Almox EsFO – Almoxarifado da Escola de Formação de Oficiais – APMG');
const F1=await pdf.embedFont(P.StandardFonts.Helvetica),F2=await pdf.embedFont(P.StandardFonts.HelveticaBold);
const W=paisagem?841.89:595.28,H=paisagem?595.28:841.89,M=40,azul=P.rgb(0,0.204,0.471),ouro=P.rgb(0.94,0.75,0.13),cinza=P.rgb(0.33,0.39,0.48),preto=P.rgb(0.08,0.13,0.18),linha=P.rgb(0.83,0.86,0.91),claro=P.rgb(0.95,0.96,0.98),verm=P.rgb(0.75,0.15,0.1);
let pg,y;
const nova=()=>{pg=pdf.addPage([W,H]);y=H-M;};
const quebra=(t,f,s,w)=>{const out=[];for(const par of winAnsi(t).split('\n')){let l='';for(const pal of par.split(' ')){const tt=l?l+' '+pal:pal;if(l&&f.widthOfTextAtSize(tt,s)>w){out.push(l);l=pal;}else l=tt;}out.push(l);}return out;};
const cabe=h=>{if(y-h<M+24){nova();return true;}return false;};
const texto=(t,o={})=>{const f=o.f||F1,s=o.s||9,x=o.x||M,w=o.w||(W-2*M),c=o.c||preto;for(const l of quebra(t,f,s,w)){cabe(s*1.35);pg.drawText(l,{x,y:y-s,size:s,font:f,color:c});y-=s*1.35;}};
const kv=(k,v)=>{if(v==null||v==='')return;const kw=140,ks=quebra(k,F2,8.5,kw-10),ls=quebra(String(v),F1,9,W-2*M-kw),alt=Math.max(12*ls.length,11*ks.length);cabe(alt);ks.forEach((l,i)=>pg.drawText(l,{x:M,y:y-9-i*11,size:8.5,font:F2,color:cinza}));ls.forEach((l,i)=>pg.drawText(l,{x:M+kw,y:y-9-i*12,size:9,font:F1,color:preto}));y-=alt+1;};
const secao=(t,extra)=>{cabe(40);y-=6;pg.drawLine({start:{x:M,y},end:{x:W-M,y},thickness:1.2,color:azul});y-=6;texto(t,{f:F2,s:12});if(extra)texto(extra,{s:8.5,c:cinza});y-=2;};
/* tabela: cols=[{t:'Título',w:fração,a:'r'}], linhas=[[...]], opções {destaque:i=>bool} */
const tabela=(cols,linhas,o={})=>{
const larg=W-2*M,tot=cols.reduce((a,c)=>a+c.w,0),ws=cols.map(c=>c.w/tot*larg),s=8.5,pad=4;
const cab=()=>{const h=16;cabe(h+14);let x=M;pg.drawRectangle({x:M,y:y-h,width:larg,height:h,color:azul});
cols.forEach((c,i)=>{const t=quebra(c.t,F2,7.8,ws[i]-2*pad)[0]||'';const tw=F2.widthOfTextAtSize(t,7.8);pg.drawText(t,{x:c.a==='r'?x+ws[i]-pad-tw:x+pad,y:y-11,size:7.8,font:F2,color:P.rgb(1,1,1)});x+=ws[i];});y-=h;};
cab();
linhas.forEach((ln,k)=>{const cel=ln.map((v,i)=>quebra(v==null?'':String(v),F1,s,ws[i]-2*pad));const h=Math.max(...cel.map(c=>c.length))*11+6;
if(cabe(h))cab();
if(k%2)pg.drawRectangle({x:M,y:y-h,width:larg,height:h,color:claro});
let x=M;const red=o.destaque&&o.destaque(k);
cel.forEach((ls,i)=>{ls.forEach((l,j)=>{const tw=F1.widthOfTextAtSize(l,s);pg.drawText(l,{x:cols[i].a==='r'?x+ws[i]-pad-tw:x+pad,y:y-11-j*11,size:s,font:(o.negrito&&o.negrito(k,i))?F2:F1,color:red?verm:preto});});x+=ws[i];});
y-=h;pg.drawLine({start:{x:M,y},end:{x:W-M,y},thickness:.4,color:linha});});
if(!linhas.length)texto('Nenhum registro.',{s:9,c:cinza});
y-=6;
};
nova();
pg.drawRectangle({x:0,y:H-78,width:W,height:78,color:azul});pg.drawRectangle({x:0,y:H-81,width:W,height:3,color:ouro});
const br=await brasaoPDF(pdf);let tx=M;
if(br){const h=60,w=h*br.width/br.height;pg.drawImage(br,{x:M,y:H-39-h/2,width:w,height:h});tx=M+w+14;}
pg.drawText('ALMOX ESFO',{x:tx,y:H-38,size:20,font:F2,color:P.rgb(1,1,1)});
pg.drawText(winAnsi('Almoxarifado da Escola de Formação de Oficiais – APMG – PMPR'),{x:tx,y:H-56,size:9.5,font:F1,color:P.rgb(0.88,0.92,0.98)});
y=H-100;
texto(titulo,{f:F2,s:15});
texto(`Gerado em ${fmt(nowISO())} por ${nomeM(sess.userId)}${sub?' · '+sub:''}`,{s:9,c:cinza});y-=6;
await desenhar({texto,kv,tabela,secao,cinza,F1,F2});
const pags=pdf.getPages();pags.forEach((p,i)=>{p.drawLine({start:{x:M,y:30},end:{x:W-M,y:30},thickness:.5,color:linha});
p.drawText(winAnsi(`${NOME} – ${titulo}`).slice(0,110),{x:M,y:18,size:7.5,font:F1,color:cinza});
p.drawText(`${i+1} / ${pags.length}`,{x:W-M-30,y:18,size:7.5,font:F1,color:cinza});});
baixar(`almox-esfo-${arq}-${carimboArq()}.pdf`,await pdf.save(),'application/pdf');
toast('Relatório PDF gerado.');
}
const tamTxtPdf=t=>tamTxt(t)||'Único';
/* ----- Tela de relatórios ----- */
function vRelatorios(){
const hj=dataInput(nowISO()),ini=dataInput(new Date(Date.now()-30*864e5).toISOString());
const R=[['estoque','Estoque do almoxarifado','Itens por categoria e tamanho: na prateleira, em uso e total.',''],
['uso','Material em uso','Todas as cautelas ativas, por militar, com prazo e assinatura.',''],
['atraso','Cautelas em atraso','Cautelas com prazo de devolução vencido.',''],
['periodo','Movimentação no período','Cautelas abertas, entregues, devolvidas e transferidas entre duas datas.','periodo'],
['ocorr','Danos e extravios','Ocorrências registradas nas devoluções.','periodo'],
['militar','Ficha do militar','Material em aberto e histórico de um militar.','militar']];
return `<div class="a-head"><div><h1>Relatórios</h1><p>Relatórios em PDF com o cabeçalho do almoxarifado, prontos para imprimir ou arquivar.</p></div></div>
<div class="it-lista">${R.map(([k,t,d,extra])=>`<form class="it-row" id="f-rel-${k}" data-rel="${k}"><div><h3>${t}</h3><p class="resumo">${d}</p>
${extra==='periodo'?`<div class="row" style="margin-top:.5rem"><label class="f"><span>De</span><input class="i" type="date" name="de" value="${ini}"></label><label class="f"><span>Até</span><input class="i" type="date" name="ate" value="${hj}"></label></div>`:''}
${extra==='militar'?`<label class="f" style="margin-top:.5rem"><span>Militar</span><select class="i" name="mil" required><option value="">Escolha…</option>${D.users.filter(u=>!u.pendente).sort((a,b)=>nomeU(a).localeCompare(nomeU(b),'pt-BR')).map(u=>`<option value="${u.id}">${esc(nomeU(u))} – ${esc(turmaU(u))}</option>`).join('')}</select></label>`:''}</div>
<div class="acts"><button class="btn btn-pri">Gerar PDF</button></div></form>`).join('')}</div>`;
}
async function gerarRelatorio(form,fd){
const k=form.dataset.rel;
const de=fd.get('de')?new Date(fd.get('de')+'T00:00:00').toISOString():null,ate=fd.get('ate')?new Date(fd.get('ate')+'T23:59:59').toISOString():null;
const periodoTxt=de?`de ${fmtD(de)} a ${fmtD(ate)}`:'';
if((k==='periodo'||k==='ocorr'||k==='militar')&&!ui.histTudo)await carregarHistTudo(true);
const todas=ui.histTudo?baldes.tudo.concat(D.cautelas.filter(c=>!baldes.tudo.some(x=>x.id===c.id))):D.cautelas;
const linhasCaut=c=>(c.status==='cautelada'?pendentes(c):c.itens||[]).map(l=>`${c.status==='cautelada'?pend(l):l.qtd}× ${l.nome}${tamTxt(l.tam)?' ('+l.tam+')':''}`).join('\n');
if(k==='estoque')return gerarPDF('Estoque do almoxarifado','',`estoque`,async T=>{
let g={tot:0,dis:0,uso:0};
D.cats.concat(D.itens.some(i=>!D.cats.some(c=>c.id===i.catId))?[{id:null,nome:'Sem categoria'}]:[]).forEach(c=>{
const its=D.itens.filter(i=>c.id?i.catId===c.id:!D.cats.some(x=>x.id===i.catId));if(!its.length)return;
const r=c.id?resumoCat(c):{tot:0,dis:0,uso:0};g.tot+=r.tot;g.dis+=r.dis;g.uso+=r.uso;
T.secao(c.nome,c.id?`${its.length} item(ns) · ${r.dis} na prateleira · ${r.uso} em uso · total ${r.tot}`:'');
const linhas=[];its.forEach(it=>(it.tamanhos||[]).forEach((t,j)=>{const e=est(it,t);linhas.push([j?'':it.nome,tamTxtPdf(t),e.disp,cauteladoDe(it.id,t),e.total,(UNID[it.unidade]||UNID.un)[1]]);}));
T.tabela([{t:'Item',w:5},{t:'Tamanho',w:1.4},{t:'Prateleira',w:1.3,a:'r'},{t:'Em uso',w:1.2,a:'r'},{t:'Total',w:1.1,a:'r'},{t:'Unidade',w:1.4}],linhas,{destaque:i=>linhas[i][4]>0&&linhas[i][2]<=0,negrito:(i,col)=>col===0});
});
T.secao('Resumo geral');T.kv('Peças na prateleira',g.dis);T.kv('Peças em uso',g.uso);T.kv('Total do almoxarifado',g.tot);
T.texto('Linhas em vermelho: tamanho esgotado na prateleira.',{s:8,c:T.cinza});
});
if(k==='uso'||k==='atraso'){
let l=ativasA();if(k==='atraso')l=l.filter(atrasada);
l.sort((a,b)=>nomeM(a.userId).localeCompare(nomeM(b.userId),'pt-BR'));
if(!l.length){toast(k==='atraso'?'Não há cautelas em atraso.':'Não há material em uso.',true);return;}
return gerarPDF(k==='atraso'?'Cautelas em atraso':'Material em uso',`${l.length} cautela(s)`,k,async T=>{
T.tabela([{t:'Nº',w:.9},{t:'Militar',w:2.6},{t:'Turma / OPM',w:2},{t:'Material em uso',w:4},{t:'Desde',w:1.2},{t:'Devolver até',w:1.3}],
l.map(c=>{const u=user(c.userId);return [nr(c.num),nomeU(u),turmaU(u),linhasCaut(c),fmtD(c.entregueEm||c.criadoEm),c.prazo?fmtD(c.prazo)+(atrasada(c)?' (atraso)':''):'sem prazo'];}),{destaque:i=>atrasada(l[i])});
const soma={};l.forEach(c=>pendentes(c).forEach(x=>{const kk=x.nome+'|'+x.tam;soma[kk]=soma[kk]||[x.nome,tamTxtPdf(x.tam),0];soma[kk][2]+=pend(x);}));
T.secao('Totais por item');T.tabela([{t:'Item',w:5},{t:'Tamanho',w:1.5},{t:'Peças',w:1,a:'r'}],Object.values(soma).sort((a,b)=>a[0].localeCompare(b[0],'pt-BR')));
},true);}
if(k==='periodo'){
const ev=[];todas.forEach(c=>(c.log||[]).forEach(x=>{if(x.t>=de&&x.t<=ate)ev.push({c,x});}));
ev.sort((a,b)=>String(a.x.t).localeCompare(String(b.x.t)));
if(!ev.length){toast('Nenhuma movimentação no período.',true);return;}
return gerarPDF('Movimentação no período',periodoTxt,'movimentacao',async T=>{
const cont={};ev.forEach(e=>cont[e.x.a]=(cont[e.x.a]||0)+1);
T.secao('Resumo');Object.entries(cont).forEach(([a,n])=>T.kv(a,n));
T.secao('Eventos');T.tabela([{t:'Data',w:1.5},{t:'Nº',w:.9},{t:'Militar',w:2.3},{t:'Evento',w:2},{t:'Material',w:3.6},{t:'Por',w:1.8}],
ev.map(({c,x})=>[fmt(x.t),nr(c.num),nomeM(c.userId),x.a+(x.obs?'\n'+x.obs:''),linhasCaut({...c,status:'x'}),nomeM(x.por)]));
},true);}
if(k==='ocorr'){
const oc=[];todas.forEach(c=>(c.ocorrencias||[]).forEach(o=>{if(o.t>=de&&o.t<=ate)oc.push({c,o});}));
if(!oc.length){toast('Nenhum dano ou extravio no período.',true);return;}
return gerarPDF('Danos e extravios',periodoTxt,'ocorrencias',async T=>{
T.tabela([{t:'Data',w:1.4},{t:'Nº',w:.9},{t:'Militar',w:2.3},{t:'Item',w:3},{t:'Qtd',w:.6,a:'r'},{t:'Situação',w:1.3},{t:'Observação',w:3}],
oc.map(({c,o})=>[fmt(o.t),nr(c.num),nomeM(c.userId),o.nome+(tamTxt(o.tam)?' ('+o.tam+')':''),o.qtd,o.estado,o.obs||'']));
},true);}
if(k==='militar'){
const id=fd.get('mil');const u=user(id);const cs=todas.filter(c=>c.userId===id).sort((a,b)=>String(b.criadoEm).localeCompare(String(a.criadoEm)));
const abertas=cs.filter(c=>c.status==='cautelada'||c.status==='separada');
return gerarPDF('Ficha do militar',nomeU(u),'ficha-'+norm(u.guerra||'militar').replace(/\W+/g,''),async T=>{
T.secao('Identificação');T.kv('Militar',`${nomeU(u)} – ${u.nome||''}`);T.kv('RG',u.rg);T.kv(u.tipo==='oficial'?'OPM':'Turma',u.tipo==='oficial'?u.opm:[u.turma,turmaU(u)].filter(Boolean).join(' · '));T.kv('E-mail',u.email);T.kv('Telefone',u.telefone);
T.secao('Romaneio');ROM.forEach(([kk,n])=>T.kv(n,(u.romaneio||{})[kk]||'—'));
T.secao('Material em aberto',abertas.length?'':'Nada consta: nenhum material pendente de devolução.');
if(abertas.length)T.tabela([{t:'Nº',w:.9},{t:'Material',w:5},{t:'Prazo',w:1.4},{t:'Assinatura',w:2.6}],abertas.map(c=>[nr(c.num),linhasCaut(c),c.prazo?fmtD(c.prazo):'sem prazo',c.assinatura?fmt(c.assinatura.em)+' – '+(c.assinatura.metodo||''):'pendente']));
T.secao('Histórico de cautelas');T.tabela([{t:'Nº',w:.9},{t:'Situação',w:1.6},{t:'Material',w:5},{t:'Atualizada',w:1.6}],cs.map(c=>[nr(c.num),(ST[c.status]||[c.status])[0],linhasCaut({...c,status:'x'}),fmt(c.atualizadoEm||c.criadoEm)]));
});}
}
/* Termo de cautela e nada consta também em PDF */
async function termoPDF(id){
const c=C(id);if(!c)return;const u=user(c.userId);const a=c.assinatura||{};
await gerarPDF(`Termo de cautela ${nr(c.num)}`,'',`termo-${c.num}`,async T=>{
T.secao('Militar');T.kv('Militar',`${nomeU(u)} – ${u.nome||''}`);T.kv('RG',u.rg);T.kv(u.tipo==='oficial'?'OPM':'Turma',u.tipo==='oficial'?u.opm:[u.turma,turmaU(u)].filter(Boolean).join(' · '));
T.kv('Devolver até',c.prazo?fmtD(c.prazo):'Sem prazo definido');T.kv('Situação',(ST[c.status]||[c.status])[0]);
T.secao('Material');T.tabela([{t:'Item',w:5},{t:'Tamanho',w:1.4},{t:'Qtd',w:.8,a:'r'},{t:'Devolvido',w:1.2,a:'r'},{t:'Transferido',w:1.3,a:'r'}],(c.itens||[]).map(x=>[x.nome+(x.consumo?' (entrega definitiva)':''),tamTxtPdf(x.tam),x.qtd,x.dev||0,x.trf||0]));
T.texto(`Declaro que recebi do Almoxarifado da Escola de Formação de Oficiais o material acima relacionado, em perfeitas condições de uso, comprometendo-me a zelar por sua guarda e conservação e a devolvê-lo ${c.prazo?'até '+fmtD(c.prazo):'quando solicitado'}, ciente de que responderei pelo extravio ou dano causado por mau uso.`,{s:9.5});
T.secao('Assinatura eletrônica');T.kv('Assinado por',nomeM(a.por||c.userId));T.kv('Data e hora',fmt(a.em));T.kv('Forma',FORMA[a.metodo]||a.metodo||'');T.kv('Código (SHA-256)',a.hash);T.kv('Texto assinado',a.dados);
if((c.log||[]).length){T.secao('Andamento');T.tabela([{t:'Data',w:1.5},{t:'Evento',w:2.2},{t:'Por',w:2},{t:'Observação',w:3.5}],c.log.map(x=>[fmt(x.t),x.a,nomeM(x.por),x.obs||'']));}
});
}
async function nadaConstaPDF(id){
const u=user(id);const uso=D.cautelas.filter(c=>c.userId===id&&(c.status==='cautelada'||c.status==='separada'));
await gerarPDF(uso.length?'Material pendente de devolução':'Declaração de nada consta','',(uso.length?'pendencias-':'nada-consta-')+norm(u.guerra||'').replace(/\W+/g,''),async T=>{
T.secao('Militar');T.kv('Militar',`${nomeU(u)} – ${u.nome||''}`);T.kv('RG',u.rg);T.kv(u.tipo==='oficial'?'OPM':'Turma',u.tipo==='oficial'?u.opm:[u.turma,turmaU(u)].filter(Boolean).join(' · '));
if(!uso.length){T.secao('Declaração');T.texto('Declaro, para os devidos fins, que NADA CONSTA em nome do militar acima identificado no Almoxarifado da Escola de Formação de Oficiais, não havendo material cautelado pendente de devolução até a presente data.',{s:10.5});
T.texto('\n\n\n_____________________________________________',{s:10});T.texto(nomeM(sess.userId),{s:10,f:T.F2});T.texto('Responsável pelo Almoxarifado – EsFO',{s:9});}
else{T.secao('Material pendente');T.tabela([{t:'Nº',w:.9},{t:'Item',w:4.5},{t:'Tamanho',w:1.3},{t:'Qtd',w:.8,a:'r'},{t:'Prazo',w:1.4}],
uso.flatMap(c=>(c.status==='separada'?c.itens:pendentes(c)).map(x=>[nr(c.num),x.nome,tamTxtPdf(x.tam),c.status==='separada'?x.qtd:pend(x),c.prazo?fmtD(c.prazo):'—'])));}
});
}

/* ============ Importar material por planilha do Excel (como no SICAM) ============ */
async function carregarXLSX(){
if(window.XLSX)return window.XLSX;
await new Promise((res,rej)=>{const sc=document.createElement('script');sc.src='https://cdnjs.cloudflare.com/ajax/libs/xlsx/0.18.5/xlsx.full.min.js';
sc.onload=res;sc.onerror=()=>rej({msg:'Não foi possível carregar o leitor de planilhas. Confira a internet.'});document.head.appendChild(sc);});
return window.XLSX;
}
const SIN_IMP=[['categoria',['categoria','grupo','classe']],['item',['item','material','nome','descricao','denominacao','peca']],['tamanho',['tamanho','tam','numero','numeracao','medida']],
['qtd',['quantidade','qtd','qtde','quant','estoque','saldo']],['unidade',['unidade','un','und']],['romaneio',['romaneio','sugerirtamanho','campo']],['definitiva',['entregadefinitiva','definitiva','consumo']]];
const chave=s=>norm(s).replace(/[^a-z0-9]/g,'');
function mapaImp(cab){const m={};cab.forEach((h,i)=>{const k=chave(h);for(const [campo,sins] of SIN_IMP){if(m[campo]==null&&sins.some(x=>k===x||k.startsWith(x))){m[campo]=i;break;}}});return m;}
async function baixarModelo(){
try{const X=await carregarXLSX();
const linhas=[['Categoria','Item','Tamanho','Quantidade','Unidade','Romaneio','Entrega definitiva'],
['Calçados','Sapato social','41',10,'par','calcado','não'],['Calçados','Sapato social','42',8,'par','calcado','não'],
['Luvas','Luva branca','M',20,'par','luva','não'],['Uniforme de desfile','Túnica branca do uniforme especial de desfile','G',5,'un','gandola','não'],
['Acessórios','Forragê','Único',30,'un','','não']];
const ws=X.utils.aoa_to_sheet(linhas);ws['!cols']=[{wch:24},{wch:46},{wch:10},{wch:12},{wch:10},{wch:12},{wch:18}];
const inst=X.utils.aoa_to_sheet([['Como preencher'],['Uma linha por item e tamanho. Para itens sem tamanho, escreva "Único" ou deixe em branco.'],
['Categoria e Item: se não existirem no sistema, serão criados. Escreva o nome igual ao que já existe para somar ao mesmo item.'],
['Quantidade: número de peças (ou pares) que estão entrando no almoxarifado.'],['Unidade: un, par ou conj. Romaneio (opcional): gandola, camisa, calca, calcado, cobertura, luva ou cinto.'],
['Entrega definitiva (opcional): "sim" para material que o militar não devolve.']]);inst['!cols']=[{wch:110}];
const wb=X.utils.book_new();X.utils.book_append_sheet(wb,ws,'Material');X.utils.book_append_sheet(wb,inst,'Instruções');
X.writeFile(wb,'modelo-importacao-almox-esfo.xlsx');}catch(e){toast(erroFirebase(e),true);}
}
function abrirImportar(){
ui.imp=null;
openModal('Importar material de planilha',`<form id="f-imp" class="stack">
<p class="small">Use uma planilha do Excel com as colunas <b>Categoria, Item, Tamanho e Quantidade</b> (Unidade, Romaneio e Entrega definitiva são opcionais). <button type="button" class="link" data-act="modeloImp">Baixar planilha modelo</button></p>
<label class="f"><span>Arquivo (.xlsx, .xls ou .csv)</span><input class="i" type="file" id="imp-arq" accept=".xlsx,.xls,.csv" data-chgimp="1"></label>
<div class="seg" role="group"><button type="button" data-act="impModo" data-m="somar" aria-pressed="${(ui.impModo||'somar')==='somar'}">Somar ao estoque (entrada)</button><button type="button" data-act="impModo" data-m="substituir" aria-pressed="${ui.impModo==='substituir'}">Substituir pela planilha (inventário)</button></div>
<div id="imp-previa"><p class="small muted">Escolha o arquivo para ver a prévia. Nada é gravado antes de você confirmar.</p></div>
<label class="f"><span>Origem / documento</span><input class="i" name="obs" placeholder="Ex.: Inventário inicial 2026"></label>
<p class="erro" id="imp-erro"></p></form>`,`<button class="btn" data-act="fechar">Cancelar</button><button class="btn btn-pri" data-act="confirmarImp" id="imp-ok" disabled>Importar</button>`);
}
async function lerImportacao(file){
const err=m=>{$('#imp-erro').textContent=m;};err('');
try{const X=await carregarXLSX();const wb=X.read(await file.arrayBuffer(),{type:'array'});
const aba=wb.SheetNames.find(n=>norm(n).startsWith('material'))||wb.SheetNames[0];
const rows=X.utils.sheet_to_json(wb.Sheets[aba],{header:1,defval:'',raw:false}).filter(r=>r.some(v=>String(v).trim()!==''));
if(rows.length<2)return err('A planilha está vazia.');
const hi=rows.findIndex(r=>{const m=mapaImp(r);return m.item!=null&&m.qtd!=null;});if(hi<0)return err('Não encontrei as colunas "Item" e "Quantidade". Use a planilha modelo.');
const m=mapaImp(rows[hi]);const g=(r,c)=>m[c]==null?'':String(r[m[c]]==null?'':r[m[c]]).trim();
const linhas=[];const erros=[];
rows.slice(hi+1).forEach((r,i)=>{const nome=g(r,'item');if(!nome)return;const q=parseInt(String(g(r,'qtd')).replace(/\D/g,''),10);
if(isNaN(q)||q<0){erros.push(`Linha ${hi+i+2}: quantidade inválida`);return;}
let tam=g(r,'tamanho').toUpperCase();if(!tam||norm(tam)==='unico')tam='Único';
const un=chave(g(r,'unidade'));const rom=chave(g(r,'romaneio'));
linhas.push({cat:g(r,'categoria')||'Outros',nome,tam,q,unidade:un.startsWith('par')?'par':un.startsWith('conj')?'conj':'un',campo:ROM.some(([k])=>k===rom)?rom:'',consumo:/^s/.test(chave(g(r,'definitiva')))});});
if(!linhas.length)return err('Nenhuma linha com item e quantidade.'+(erros.length?' '+erros.join('; '):''));
// agrupa por categoria + item + tamanho
const ag={};linhas.forEach(l=>{const k=chave(l.cat)+'|'+chave(l.nome)+'|'+l.tam;if(ag[k])ag[k].q+=l.q;else ag[k]={...l};});
ui.imp={linhas:Object.values(ag),erros,arq:file.name};desenharPreviaImp();
}catch(e){console.error(e);err(erroFirebase(e));}
}
function planoImp(){
const novasCat={},novosItens={};
return ui.imp.linhas.map(l=>{const c=D.cats.find(x=>chave(x.nome)===chave(l.cat));const it=c?D.itens.find(x=>x.catId===c.id&&chave(x.nome)===chave(l.nome)):null;
const st=[];if(!c&&!novasCat[chave(l.cat)]){st.push('nova categoria');novasCat[chave(l.cat)]=1;}
if(!it&&!novosItens[chave(l.cat)+chave(l.nome)]){st.push('novo item');novosItens[chave(l.cat)+chave(l.nome)]=1;}
else if(it&&!(it.tamanhos||[]).includes(l.tam))st.push('novo tamanho');
const atual=it?est(it,l.tam).disp:0;return {...l,c,it,st,atual};});
}
function desenharPreviaImp(){
const p=planoImp();const modo=ui.impModo||'somar';
$('#imp-previa').innerHTML=`<p class="small"><b>${esc(ui.imp.arq)}</b>: ${p.length} linha(s)${ui.imp.erros.length?` · <span class="c-stamp">${ui.imp.erros.length} ignorada(s)</span>`:''}</p>
<div class="tbl-wrap" style="max-height:300px;overflow:auto"><table><thead><tr><th>Categoria</th><th>Item</th><th>Tam.</th><th>Prateleira hoje</th><th>${modo==='somar'?'Entrada':'Nova contagem'}</th><th></th></tr></thead><tbody>
${p.map(l=>`<tr><td>${esc(l.cat)}</td><td>${esc(l.nome)}</td><td>${esc(l.tam)}</td><td>${l.atual}</td><td><b>${modo==='somar'?'+'+l.q:l.q}</b></td><td>${l.st.map(s=>`<span class="tag">${s}</span>`).join(' ')}</td></tr>`).join('')}</tbody></table></div>
${ui.imp.erros.length?`<p class="small c-stamp">${ui.imp.erros.map(esc).join('<br>')}</p>`:''}`;
const b=$('#imp-ok');if(b)b.disabled=!p.length;
}
async function confirmarImp(){
if(!ui.imp)return;const modo=ui.impModo||'somar';const obs=String(($('#f-imp [name=obs]')||{}).value||'').trim()||('Planilha '+ui.imp.arq);
const p=planoImp();const b=writeBatch(db);const catIds={},itens={};let ordC=(D.cats.length+1)*10;
p.forEach(l=>{
let cid=l.c?l.c.id:catIds[chave(l.cat)];
if(!cid){cid=uidNovo();catIds[chave(l.cat)]=cid;const nc={id:cid,nome:l.cat};b.set(doc(db,'categorias',cid),{nome:l.cat,ordem:ordC,icone:icCat(nc)});ordC+=10;}
const ki=cid+'|'+chave(l.nome);
if(!itens[ki]){const it=l.it;itens[ki]=it?{id:it.id,novo:false,o:{tamanhos:[...(it.tamanhos||[])],estoque:JSON.parse(JSON.stringify(it.estoque||{}))},nome:it.nome}
:{id:uidNovo(),novo:true,nome:l.nome,o:{catId:cid,nome:l.nome,unidade:l.unidade,campo:l.campo,tamanhos:[],estoque:{},consumo:l.consumo,ativo:true,ordem:D.itens.filter(i=>i.catId===cid).length*10},mov:{}};itens[ki].mov=itens[ki].mov||{};}
const x=itens[ki];if(!x.o.tamanhos.includes(l.tam))x.o.tamanhos.push(l.tam);
const e=x.o.estoque[l.tam]||{total:0,disp:0};
if(modo==='somar'){e.total+=l.q;e.disp+=l.q;x.mov[l.tam]=(x.mov[l.tam]||0)+l.q;}else{const d=l.q-e.disp;e.disp=l.q;e.total=Math.max(0,e.total+d);x.mov[l.tam]=d;}
x.o.estoque[l.tam]=e;});
Object.values(itens).forEach(x=>{if(x.o.tamanhos.length>1&&!((x.o.estoque['Único']||{}).total>0)){x.o.tamanhos=x.o.tamanhos.filter(t=>t!=='Único');delete x.o.estoque['Único'];}
if(x.novo)b.set(doc(db,'itens',x.id),x.o);else b.update(doc(db,'itens',x.id),{tamanhos:x.o.tamanhos,estoque:x.o.estoque});
b.set(doc(collection(db,'movimentos')),{t:nowISO(),tipo:modo==='somar'?'entrada':'inventario',itemId:x.id,nome:x.nome,tams:x.mov,obs:obs+' (importação)',por:sess.userId});});
try{await b.commit();closeModal();ui.imp=null;toast(`Importação concluída: ${p.length} linha(s).`);}catch(e){$('#imp-erro').textContent=erroFirebase(e);}
}
