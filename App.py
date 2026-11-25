"""
Auditax 360º Enterprise — v2.0
Bloqueadores SaaS resolvidos:
  1. Multitenancy real (tenant_id em todo schema)
  2. Gestão de usuários (cadastro, papéis, convite, troca de senha)
  3. Processamento assíncrono (threading + fila por tenant)
  4. Controle de plano/billing (limites, trial, quotas)
  5. Banco robusto (PostgreSQL-ready; SQLite em dev com WAL + pool guard)
"""

import streamlit as st
import pandas as pd
import io
import plotly.express as px
import logging
import threading
import queue
import time
import uuid
import secrets
import string
from datetime import datetime, timedelta
from decimal import Decimal
import hashlib
import tempfile
import os
import json
import bcrypt
import smtplib
import re
import unicodedata
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from collections import defaultdict

# ── configuração de e-mail (via variáveis de ambiente) ─────────────────────────
SMTP_HOST     = os.environ.get("SMTP_HOST", "")
SMTP_PORT     = int(os.environ.get("SMTP_PORT", "587"))
SMTP_USER     = os.environ.get("SMTP_USER", "")
SMTP_PASS     = os.environ.get("SMTP_PASS", "")
EMAIL_FROM    = os.environ.get("EMAIL_FROM", SMTP_USER)
NOTIF_ENABLED = bool(SMTP_HOST and SMTP_USER and SMTP_PASS)

# ── tabela de alíquotas ICMS interestaduais por UF de destino ─────────────────
# Fonte: Resolução SF nº 22/1989 + EC 87/2015
ALIQ_INTERESTADUAL: dict[str, float] = {
    "AC":7.0,"AL":7.0,"AM":7.0,"AP":7.0,"BA":7.0,"CE":7.0,"DF":7.0,
    "ES":7.0,"GO":7.0,"MA":7.0,"MG":12.0,"MS":7.0,"MT":7.0,"PA":7.0,
    "PB":7.0,"PE":7.0,"PI":7.0,"PR":12.0,"RJ":12.0,"RN":7.0,"RO":7.0,
    "RR":7.0,"RS":12.0,"SC":12.0,"SE":7.0,"SP":12.0,"TO":7.0,
}
# CSTs que exigem ICMS-ST preenchido (substituição tributária)
CST_COM_ST = {"10","30","60","70","90"}
# CFOPs de crédito indevido (uso e consumo / ativo fixo sem CIAP)
CFOP_CREDITO_INDEVIDO = {"1556","2556","1557","2557","1558","2558"}

# ── Tabela NCM × Alíquota — LC 214/2025 (Reforma Tributária) ─────────────────
# Fonte: LC 214/2025, Anexos I-V e art. 9º
# Estrutura: {prefixo_NCM: {"nome": str, "reducao_cbs": float, "reducao_ibs": float,
#                            "cbs_aliq": float, "ibs_aliq": float, "iva_aliq": float,
#                            "isento": bool, "obs": str}}
# Alíquotas de referência (art. 9º LC 214): CBS 8.8% / IBS 17.7% = IVA 26.5%
# Reduções por categoria conforme Anexos da LC 214/2025
_CBS_BASE  = 0.088   # 8,8% — alíquota plena CBS (Receita Federal)
_IBS_BASE  = 0.177   # 17,7% — alíquota plena IBS (estados + municípios)
_IVA_BASE  = 0.265   # 26,5% — IVA pleno referência

def _aliq_ncm(reducao: float) -> dict:
    """Calcula alíquotas efetivas aplicando percentual de redução."""
    return {
        "cbs_aliq":  _CBS_BASE  * (1 - reducao),
        "ibs_aliq":  _IBS_BASE  * (1 - reducao),
        "iva_aliq":  _IVA_BASE  * (1 - reducao),
        "reducao":   reducao,
    }

# Tabela NCM × categoria (prefixo 2 ou 4 dígitos)
NCM_ALIQ_REFORMA: dict[str, dict] = {
    # ── CESTA BÁSICA NACIONAL (Anexo I — alíquota zero) ──────────────────────
    "1006": {**_aliq_ncm(1.0), "nome": "Arroz",          "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "1101": {**_aliq_ncm(1.0), "nome": "Farinha de trigo","isento": True, "obs": "Cesta Básica — alíq. zero"},
    "1507": {**_aliq_ncm(1.0), "nome": "Óleo de soja",   "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0201": {**_aliq_ncm(1.0), "nome": "Carnes bovinas", "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0207": {**_aliq_ncm(1.0), "nome": "Aves (frango)",  "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0302": {**_aliq_ncm(1.0), "nome": "Peixes frescos", "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0401": {**_aliq_ncm(1.0), "nome": "Leite",          "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0405": {**_aliq_ncm(1.0), "nome": "Manteiga",       "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "1901": {**_aliq_ncm(1.0), "nome": "Misturas p/ pão","isento": True, "obs": "Cesta Básica — alíq. zero"},
    "1905": {**_aliq_ncm(1.0), "nome": "Pão/biscoitos",  "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0702": {**_aliq_ncm(1.0), "nome": "Tomate",         "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0701": {**_aliq_ncm(1.0), "nome": "Batata",         "isento": True, "obs": "Cesta Básica — alíq. zero"},
    "0706": {**_aliq_ncm(1.0), "nome": "Cenoura",        "isento": True, "obs": "Cesta Básica — alíq. zero"},

    # ── ALIMENTOS EM GERAL (Anexo II — redução 60%) ──────────────────────────
    "02":   {**_aliq_ncm(0.60), "nome": "Carnes em geral",      "isento": False, "obs": "Alimentos — 60% redução"},
    "03":   {**_aliq_ncm(0.60), "nome": "Peixes e frutos do mar","isento": False, "obs": "Alimentos — 60% redução"},
    "04":   {**_aliq_ncm(0.60), "nome": "Laticínios/ovos",      "isento": False, "obs": "Alimentos — 60% redução"},
    "07":   {**_aliq_ncm(0.60), "nome": "Hortaliças",           "isento": False, "obs": "Alimentos — 60% redução"},
    "08":   {**_aliq_ncm(0.60), "nome": "Frutas",               "isento": False, "obs": "Alimentos — 60% redução"},
    "10":   {**_aliq_ncm(0.60), "nome": "Cereais",              "isento": False, "obs": "Alimentos — 60% redução"},
    "11":   {**_aliq_ncm(0.60), "nome": "Farinhas e féculas",   "isento": False, "obs": "Alimentos — 60% redução"},
    "15":   {**_aliq_ncm(0.60), "nome": "Óleos/gorduras",       "isento": False, "obs": "Alimentos — 60% redução"},
    "16":   {**_aliq_ncm(0.60), "nome": "Conservas de carnes",  "isento": False, "obs": "Alimentos — 60% redução"},
    "17":   {**_aliq_ncm(0.60), "nome": "Açúcares",             "isento": False, "obs": "Alimentos — 60% redução"},
    "19":   {**_aliq_ncm(0.60), "nome": "Produtos de padaria",  "isento": False, "obs": "Alimentos — 60% redução"},
    "20":   {**_aliq_ncm(0.60), "nome": "Conservas de vegetais","isento": False, "obs": "Alimentos — 60% redução"},
    "21":   {**_aliq_ncm(0.60), "nome": "Prep. aliment. diversas","isento": False, "obs": "Alimentos — 60% redução"},

    # ── MEDICAMENTOS E DISPOSITIVOS MÉDICOS (Anexo III — redução 60%) ────────
    "30":   {**_aliq_ncm(0.60), "nome": "Medicamentos",          "isento": False, "obs": "Farmácia — 60% redução"},
    "9018": {**_aliq_ncm(0.60), "nome": "Instrum. médico-cirúrgicos","isento": False, "obs": "Dispositivos médicos — 60% redução"},
    "9019": {**_aliq_ncm(0.60), "nome": "Aparelhos ortopédicos", "isento": False, "obs": "Dispositivos médicos — 60% redução"},
    "9021": {**_aliq_ncm(0.60), "nome": "Artigos ortopédicos",   "isento": False, "obs": "Dispositivos médicos — 60% redução"},

    # ── HIGIENE PESSOAL E LIMPEZA (Anexo IV — redução 60% para básicos) ──────
    "3304": {**_aliq_ncm(0.60), "nome": "Produtos de beleza",    "isento": False, "obs": "Higiene — 60% redução"},
    "3305": {**_aliq_ncm(0.60), "nome": "Xampus/condicionadores","isento": False, "obs": "Higiene — 60% redução"},
    "3401": {**_aliq_ncm(0.60), "nome": "Sabões e detergentes",  "isento": False, "obs": "Higiene — 60% redução"},
    "3402": {**_aliq_ncm(0.60), "nome": "Tensoativos/limpeza",   "isento": False, "obs": "Higiene — 60% redução"},
    "9619": {**_aliq_ncm(0.60), "nome": "Absorventes higiênicos","isento": False, "obs": "Higiene — 60% redução"},
    "4818": {**_aliq_ncm(0.60), "nome": "Papel higiênico/fraldas","isento": False, "obs": "Higiene — 60% redução"},

    # ── EDUCAÇÃO E CULTURA (Anexo V — redução 60%) ───────────────────────────
    "4901": {**_aliq_ncm(0.60), "nome": "Livros impressos",      "isento": False, "obs": "Educação — 60% redução"},
    "4902": {**_aliq_ncm(0.60), "nome": "Jornais e periódicos",  "isento": False, "obs": "Educação — 60% redução"},
    "4903": {**_aliq_ncm(0.60), "nome": "Livros infantis",       "isento": False, "obs": "Educação — 60% redução"},

    # ── MOBILIDADE / TRANSPORTE (redução 60% — art. 9º §3º) ─────────────────
    "8702": {**_aliq_ncm(0.60), "nome": "Ônibus/veíc. coletivo", "isento": False, "obs": "Transporte — 60% redução"},
    "8711": {**_aliq_ncm(0.60), "nome": "Motocicletas",          "isento": False, "obs": "Transporte — 60% redução"},
    "8712": {**_aliq_ncm(0.60), "nome": "Bicicletas",            "isento": False, "obs": "Transporte — 60% redução"},

    # ── DECORAÇÃO / MÓVEIS / PRESENTES (sem redução — alíquota plena) ────────
    "94":   {**_aliq_ncm(0.00), "nome": "Móveis e artigos do lar","isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "83":   {**_aliq_ncm(0.00), "nome": "Artigos metálicos/casa", "isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "69":   {**_aliq_ncm(0.00), "nome": "Produtos cerâmicos",     "isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "70":   {**_aliq_ncm(0.00), "nome": "Vidros/cristais",        "isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "73":   {**_aliq_ncm(0.00), "nome": "Artigos de ferro/aço",   "isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "57":   {**_aliq_ncm(0.00), "nome": "Tapetes e revestimentos","isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "39":   {**_aliq_ncm(0.00), "nome": "Plásticos/artigos plast.","isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "63":   {**_aliq_ncm(0.00), "nome": "Têxteis confeccionados", "isento": False, "obs": "Decoração — alíq. plena 26,5%"},
    "97":   {**_aliq_ncm(0.00), "nome": "Arte/antiguidades",      "isento": False, "obs": "Decoração — alíq. plena 26,5%"},
}

def buscar_categoria_ncm(ncm: str) -> dict:
    """Retorna categoria e alíquotas LC 214/2025 para um NCM.
    Tenta match exato de 4 dígitos, depois 2 dígitos de capítulo, depois padrão."""
    ncm_limpo = re.sub(r"\D", "", ncm)[:8]
    if not ncm_limpo:
        return {**_aliq_ncm(0.0), "nome": "Não classificado", "isento": False, "obs": "NCM não informado — alíq. plena"}
    # Tenta 4 dígitos (posição tarifária)
    if ncm_limpo[:4] in NCM_ALIQ_REFORMA:
        return NCM_ALIQ_REFORMA[ncm_limpo[:4]]
    # Tenta 2 dígitos (capítulo)
    if ncm_limpo[:2] in NCM_ALIQ_REFORMA:
        return NCM_ALIQ_REFORMA[ncm_limpo[:2]]
    # Padrão: alíquota plena
    return {**_aliq_ncm(0.0), "nome": "Outros produtos", "isento": False,
            "obs": "Sem redução LC 214 — alíq. plena 26,5%"}

# ── banco ──────────────────────────────────────────────────────────────────────
# Tenta PostgreSQL (produção); cai para SQLite (dev/demo)
try:
    import psycopg2
    from psycopg2.extras import RealDictCursor
    _DB_URL = os.environ.get("DATABASE_URL", "")
    _USE_PG = bool(_DB_URL)
except ImportError:
    _USE_PG = False

if not _USE_PG:
    import sqlite3

# ── logging ────────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s — %(message)s"
)
log = logging.getLogger("auditax")

# ── módulos externos (plugáveis) ───────────────────────────────────────────────
try:
    from validador_reforma_2026 import ValidadorReforma2026, RegistroC170, REGIME_LUCRO_REAL
    HAS_REFORMA = True
except ImportError:
    HAS_REFORMA = False

try:
    from cruzador_xml import processar_zip_xml, cruzar_sped_vs_xml
    HAS_CRUZADOR = True
except ImportError:
    HAS_CRUZADOR = False

try:
    from biblioteca_cfop import CFOP_DB, get_cfop_descricao
    HAS_CFOP = True
except ImportError:
    CFOP_DB = {}
    HAS_CFOP = False
    def get_cfop_descricao(cfop):
        c = str(cfop).replace(".", "").strip()
        p = c[0] if c else ""
        mapa = {"1":"Entrada estadual","2":"Entrada interestadual","3":"Entrada exterior",
                "5":"Saída estadual","6":"Saída interestadual","7":"Exportação"}
        return f"{mapa.get(p,'Operação fiscal')} — CFOP {c}"

try:
    from fpdf import FPDF
    HAS_FPDF = True
except ImportError:
    HAS_FPDF = False

# ══════════════════════════════════════════════════════════════════════════════
# BLOQUEADOR 5 — BANCO ROBUSTO (PostgreSQL-ready / SQLite-WAL em dev)
# ══════════════════════════════════════════════════════════════════════════════

DB_PATH = os.environ.get("AUDITAX_DB", "auditax.db")
_db_lock = threading.Lock()   # guard extra para SQLite em modo WAL

def _get_conn():
    """Retorna conexão; PostgreSQL em produção, SQLite em dev."""
    if _USE_PG:
        conn = psycopg2.connect(_DB_URL, cursor_factory=RealDictCursor)
        return conn
    conn = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")   # suporte multi-reader
    conn.execute("PRAGMA foreign_keys=ON")
    return conn

def _ph():
    """Placeholder: %s para Postgres, ? para SQLite."""
    return "%s" if _USE_PG else "?"

def init_db():
    """Cria schema completo com suporte a multitenancy."""
    ddl = """
    -- ── BLOQUEADOR 1: tenants (multiempresa) ──────────────────────────
    CREATE TABLE IF NOT EXISTS tenants (
        id          TEXT PRIMARY KEY,
        nome        TEXT NOT NULL,
        cnpj_admin  TEXT,
        plano       TEXT NOT NULL DEFAULT 'STARTER',
        trial_ate   TEXT,
        ativo       INTEGER NOT NULL DEFAULT 1,
        criado_em   TEXT NOT NULL
    );

    -- ── BLOQUEADOR 2: usuários com papéis ─────────────────────────────
    CREATE TABLE IF NOT EXISTS usuarios (
        id           TEXT PRIMARY KEY,
        tenant_id    TEXT NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        email        TEXT NOT NULL,
        nome         TEXT NOT NULL,
        senha_hash   TEXT NOT NULL,
        papel        TEXT NOT NULL DEFAULT 'auditor',
        ativo        INTEGER NOT NULL DEFAULT 1,
        token_reset  TEXT,
        token_exp    TEXT,
        ultimo_login TEXT,
        criado_em    TEXT NOT NULL,
        UNIQUE(email, tenant_id)
    );

    -- ── BLOQUEADOR 1: empresas fiscais vinculadas ao tenant ────────────
    CREATE TABLE IF NOT EXISTS empresas (
        id          TEXT PRIMARY KEY,
        tenant_id   TEXT NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        nome        TEXT NOT NULL,
        cnpj        TEXT NOT NULL,
        uf          TEXT,
        criado_em   TEXT NOT NULL,
        UNIQUE(tenant_id, cnpj)
    );

    -- ── BLOQUEADOR 1 + 3: auditorias isoladas por tenant ──────────────
    CREATE TABLE IF NOT EXISTS auditorias (
        id               TEXT PRIMARY KEY,
        tenant_id        TEXT NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        empresa_id       TEXT REFERENCES empresas(id),
        usuario_id       TEXT REFERENCES usuarios(id),
        periodo          TEXT,
        layout_versao    TEXT,
        total_linhas     INTEGER,
        total_erros      INTEGER,
        score            INTEGER,
        vl_icms_saidas   REAL,
        vl_debitos_e110  REAL,
        divergencia_icms REAL,
        erros_graves     INTEGER,
        erros_op         INTEGER,
        erros_json       TEXT,
        status           TEXT NOT NULL DEFAULT 'concluido',
        criado_em        TEXT NOT NULL
    );

    -- ── BLOQUEADOR 4: uso mensal por tenant (quota) ────────────────────
    CREATE TABLE IF NOT EXISTS uso_mensal (
        id          TEXT PRIMARY KEY,
        tenant_id   TEXT NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        mes         TEXT NOT NULL,
        speds_proc  INTEGER NOT NULL DEFAULT 0,
        UNIQUE(tenant_id, mes)
    );

    -- ── índices ────────────────────────────────────────────────────────
    CREATE INDEX IF NOT EXISTS idx_aud_tenant   ON auditorias(tenant_id);
    CREATE INDEX IF NOT EXISTS idx_aud_empresa  ON auditorias(empresa_id);
    CREATE INDEX IF NOT EXISTS idx_usr_tenant   ON usuarios(tenant_id);
    CREATE INDEX IF NOT EXISTS idx_uso_tenant   ON uso_mensal(tenant_id, mes);

    -- ── log de acesso (LGPD) ─────────────────────────────────────────────
    CREATE TABLE IF NOT EXISTS log_acesso (
        id          TEXT PRIMARY KEY,
        tenant_id   TEXT NOT NULL,
        usuario_id  TEXT NOT NULL,
        usuario_email TEXT,
        acao        TEXT NOT NULL,
        detalhe     TEXT,
        ip          TEXT,
        criado_em   TEXT NOT NULL
    );
    CREATE INDEX IF NOT EXISTS idx_log_tenant ON log_acesso(tenant_id, criado_em);

    -- ── alertas/notificações ──────────────────────────────────────────────
    CREATE TABLE IF NOT EXISTS alertas (
        id          TEXT PRIMARY KEY,
        tenant_id   TEXT NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        empresa_id  TEXT,
        tipo        TEXT NOT NULL,
        mensagem    TEXT NOT NULL,
        lido        INTEGER NOT NULL DEFAULT 0,
        criado_em   TEXT NOT NULL
    );
    CREATE INDEX IF NOT EXISTS idx_alerta_tenant ON alertas(tenant_id, lido);
    """
    with _db_lock:
        conn = _get_conn()
        try:
            if _USE_PG:
                cur = conn.cursor()
                for stmt in ddl.split(";"):
                    s = stmt.strip()
                    if s:
                        cur.execute(s)
                conn.commit()
            else:
                conn.executescript(ddl)
            log.info("Banco inicializado.")
        finally:
            conn.close()

def _row(conn, sql, params=()):
    cur = conn.cursor()
    cur.execute(sql, params)
    r = cur.fetchone()
    return dict(r) if r else None

def _rows(conn, sql, params=()):
    cur = conn.cursor()
    cur.execute(sql, params)
    return [dict(r) for r in cur.fetchall()]

def _exec(conn, sql, params=()):
    cur = conn.cursor()
    cur.execute(sql, params)

init_db()

# ══════════════════════════════════════════════════════════════════════════════
# BLOQUEADOR 4 — PLANOS E CONTROLE DE QUOTA
# ══════════════════════════════════════════════════════════════════════════════

PLANOS = {
    "TRIAL":       {"label": "Trial (14 dias)", "speds_mes": 5,   "usuarios": 2,  "historico_meses": 3},
    "STARTER":     {"label": "Starter",          "speds_mes": 20,  "usuarios": 3,  "historico_meses": 6},
    "PROFISSIONAL":{"label": "Profissional",      "speds_mes": 100, "usuarios": 10, "historico_meses": 24},
    "ENTERPRISE":  {"label": "Enterprise",        "speds_mes": 9999,"usuarios": 999,"historico_meses": 999},
}

def get_plano(tenant: dict) -> dict:
    """Retorna config do plano, levando trial em conta."""
    if tenant.get("trial_ate"):
        try:
            exp = datetime.fromisoformat(tenant["trial_ate"])
            if datetime.now() <= exp:
                return {**PLANOS["TRIAL"], "nome": "TRIAL", "trial_restante": (exp - datetime.now()).days}
        except Exception:
            pass
    nome = tenant.get("plano", "STARTER")
    return {**PLANOS.get(nome, PLANOS["STARTER"]), "nome": nome}

def verificar_quota(tenant_id: str, plano: dict) -> tuple[bool, str]:
    """Retorna (pode_processar, mensagem)."""
    mes_atual = datetime.now().strftime("%Y-%m")
    limite = plano["speds_mes"]
    with _db_lock:
        conn = _get_conn()
        try:
            row = _row(conn, f"SELECT speds_proc FROM uso_mensal WHERE tenant_id={_ph()} AND mes={_ph()}", (tenant_id, mes_atual))
            usado = row["speds_proc"] if row else 0
        finally:
            conn.close()
    if usado >= limite:
        return False, f"Limite de {limite} SPEDs/mês atingido no plano {plano['nome']}. Faça upgrade para continuar."
    return True, f"{usado}/{limite} SPEDs processados este mês."

def registrar_uso(tenant_id: str):
    mes = datetime.now().strftime("%Y-%m")
    p = _ph()
    with _db_lock:
        conn = _get_conn()
        try:
            existing = _row(conn, f"SELECT id FROM uso_mensal WHERE tenant_id={p} AND mes={p}", (tenant_id, mes))
            if existing:
                _exec(conn, f"UPDATE uso_mensal SET speds_proc=speds_proc+1 WHERE tenant_id={p} AND mes={p}", (tenant_id, mes))
            else:
                _exec(conn, f"INSERT INTO uso_mensal(id,tenant_id,mes,speds_proc) VALUES({p},{p},{p},1)",
                      (str(uuid.uuid4()), tenant_id, mes))
            conn.commit()
        finally:
            conn.close()

# ══════════════════════════════════════════════════════════════════════════════
# BLOQUEADOR 2 — GESTÃO DE USUÁRIOS
# ══════════════════════════════════════════════════════════════════════════════

PAPEIS = ["admin", "auditor", "viewer"]
PAPEIS_LABEL = {"admin": "Administrador", "auditor": "Auditor", "viewer": "Visualizador"}
PAPEIS_PERMISSOES = {
    "admin":   {"ver", "auditar", "corrigir", "usuarios", "plano"},
    "auditor": {"ver", "auditar", "corrigir"},
    "viewer":  {"ver"},
}

def _hash_senha(s: str) -> str:
    return bcrypt.hashpw(s.encode(), bcrypt.gensalt()).decode()

def _check_senha(s: str, h: str) -> bool:
    try:
        return bcrypt.checkpw(s.encode(), h.encode())
    except Exception:
        return False

def _gerar_senha_temp(n=12) -> str:
    alfa = string.ascii_letters + string.digits
    return "".join(secrets.choice(alfa) for _ in range(n))

def tem_permissao(papel: str, acao: str) -> bool:
    return acao in PAPEIS_PERMISSOES.get(papel, set())

def _normalizar_nome(nome: str) -> str:
    """Normaliza encoding Unicode NFC e remove espaços extras."""
    return unicodedata.normalize("NFC", nome.strip())

def criar_tenant(nome: str, cnpj: str = "", trial: bool = True) -> str:
    nome = _normalizar_nome(nome)
    tid = str(uuid.uuid4())
    trial_ate = (datetime.now() + timedelta(days=14)).isoformat() if trial else None
    plano = "STARTER"
    with _db_lock:
        conn = _get_conn()
        try:
            p = _ph()
            _exec(conn, f"INSERT INTO tenants(id,nome,cnpj_admin,plano,trial_ate,ativo,criado_em) VALUES({p},{p},{p},{p},{p},1,{p})",
                  (tid, nome, cnpj, plano, trial_ate, datetime.now().isoformat()))
            conn.commit()
        finally:
            conn.close()
    log.info(f"Tenant criado: {tid} ({nome})")
    return tid

def criar_usuario(tenant_id: str, email: str, nome: str, papel: str = "auditor", senha: str = None) -> tuple[str, str]:
    """Cria usuário; retorna (user_id, senha_gerada)."""
    nome = _normalizar_nome(nome)
    uid = str(uuid.uuid4())
    if not senha:
        senha = _gerar_senha_temp()
    h = _hash_senha(senha)
    with _db_lock:
        conn = _get_conn()
        try:
            p = _ph()
            _exec(conn,
                f"INSERT INTO usuarios(id,tenant_id,email,nome,senha_hash,papel,ativo,criado_em) VALUES({p},{p},{p},{p},{p},{p},1,{p})",
                (uid, tenant_id, email.lower().strip(), nome, h, papel, datetime.now().isoformat()))
            conn.commit()
        finally:
            conn.close()
    log.info(f"Usuário criado: {uid} ({email}) tenant={tenant_id}")
    return uid, senha

_login_falhas: dict[str, list] = {}   # {email: [timestamps]}
_LOGIN_MAX_TENTATIVAS = 5
_LOGIN_BLOQUEIO_MIN   = 15

def _login_bloqueado(email: str) -> tuple[bool, int]:
    """Verifica rate-limit; retorna (bloqueado, minutos_restantes)."""
    agora = datetime.now()
    janela = agora - timedelta(minutes=_LOGIN_BLOQUEIO_MIN)
    tentativas = [t for t in _login_falhas.get(email, []) if t > janela]
    _login_falhas[email] = tentativas
    if len(tentativas) >= _LOGIN_MAX_TENTATIVAS:
        mais_antiga = tentativas[0]
        restante = int((_LOGIN_BLOQUEIO_MIN * 60 - (agora - mais_antiga).total_seconds()) / 60) + 1
        return True, max(1, restante)
    return False, 0

def autenticar(email: str, senha: str) -> tuple[dict | None, dict | None, str | None]:
    """Retorna (usuario, tenant, erro) — erro é None em caso de sucesso."""
    email_lc = email.lower().strip()

    # Rate limit
    bloqueado, minutos = _login_bloqueado(email_lc)
    if bloqueado:
        return None, None, f"Conta bloqueada por tentativas excessivas. Tente em {minutos} min."

    with _db_lock:
        conn = _get_conn()
        try:
            p = _ph()
            user = _row(conn, f"SELECT * FROM usuarios WHERE email={p} AND ativo=1", (email_lc,))
            if not user or not _check_senha(senha, user["senha_hash"]):
                # Registra falha
                _login_falhas.setdefault(email_lc, []).append(datetime.now())
                falhas = len([t for t in _login_falhas[email_lc]
                              if t > datetime.now() - timedelta(minutes=_LOGIN_BLOQUEIO_MIN)])
                restam = max(0, _LOGIN_MAX_TENTATIVAS - falhas)
                msg = f"E-mail ou senha incorretos."
                if restam <= 2:
                    msg += f" {restam} tentativa(s) restante(s) antes do bloqueio."
                return None, None, msg
            tenant = _row(conn, f"SELECT * FROM tenants WHERE id={p} AND ativo=1", (user["tenant_id"],))
            if not tenant:
                return None, None, "Conta desativada. Entre em contato com o suporte."
            _exec(conn, f"UPDATE usuarios SET ultimo_login={p} WHERE id={p}", (datetime.now().isoformat(), user["id"]))
            conn.commit()
        finally:
            conn.close()

    # Limpa falhas após login bem-sucedido
    _login_falhas.pop(email_lc, None)
    log.info(f"Login: {email_lc} tenant={user['tenant_id']}")
    registrar_log(user["tenant_id"], user["id"], email_lc, "login", "Acesso ao sistema")
    return dict(user), dict(tenant), None

def listar_usuarios(tenant_id: str) -> list[dict]:
    with _db_lock:
        conn = _get_conn()
        try:
            rows = _rows(conn, f"SELECT id,email,nome,papel,ativo,ultimo_login,criado_em FROM usuarios WHERE tenant_id={_ph()} ORDER BY criado_em DESC", (tenant_id,))
        finally:
            conn.close()
    return rows

def alterar_senha(user_id: str, nova_senha: str):
    with _db_lock:
        conn = _get_conn()
        try:
            _exec(conn, f"UPDATE usuarios SET senha_hash={_ph()} WHERE id={_ph()}", (_hash_senha(nova_senha), user_id))
            conn.commit()
        finally:
            conn.close()

def desativar_usuario(user_id: str, tenant_id: str):
    with _db_lock:
        conn = _get_conn()
        try:
            _exec(conn, f"UPDATE usuarios SET ativo=0 WHERE id={_ph()} AND tenant_id={_ph()}", (user_id, tenant_id))
            conn.commit()
        finally:
            conn.close()

# seed: cria tenant + admin padrão se banco estiver vazio
def _seed():
    with _db_lock:
        conn = _get_conn()
        try:
            r = _row(conn, "SELECT COUNT(*) as n FROM tenants")
            n = r["n"] if r else 0
        finally:
            conn.close()
    if n == 0:
        tid = criar_tenant("Minha Empresa", trial=True)
        criar_usuario(tid, "admin@auditax.com", "Administrador", "admin", "admin123")
        log.info("Seed: tenant e admin padrão criados. Login: admin@auditax.com / admin123")

_seed()

# ══════════════════════════════════════════════════════════════════════════════
# BLOQUEADOR 1 — MULTITENANCY: empresas e auditorias isoladas
# ══════════════════════════════════════════════════════════════════════════════

def upsert_empresa(tenant_id: str, nome: str, cnpj: str, uf: str) -> str:
    """Cria ou atualiza empresa dentro do tenant; retorna empresa_id."""
    with _db_lock:
        conn = _get_conn()
        try:
            p = _ph()
            row = _row(conn, f"SELECT id FROM empresas WHERE tenant_id={p} AND cnpj={p}", (tenant_id, cnpj))
            if row:
                eid = row["id"]
                _exec(conn, f"UPDATE empresas SET nome={p},uf={p} WHERE id={p}", (nome, uf, eid))
            else:
                eid = str(uuid.uuid4())
                _exec(conn, f"INSERT INTO empresas(id,tenant_id,nome,cnpj,uf,criado_em) VALUES({p},{p},{p},{p},{p},{p})",
                      (eid, tenant_id, nome, cnpj, uf, datetime.now().isoformat()))
            conn.commit()
        finally:
            conn.close()
    return eid

def salvar_auditoria(tenant_id: str, usuario_id: str, dados: dict) -> str | None:
    """Persiste auditoria vinculada ao tenant. Retorna auditoria_id."""
    try:
        cnpj = dados.get("cnpj", "").strip()
        if not cnpj:
            return None
        nome = dados.get("nome_empresa", "Desconhecida").strip()
        uf = dados.get("uf_origem", "").strip()
        eid = upsert_empresa(tenant_id, nome, cnpj, uf)

        score, eg, eo = calcular_score(dados)
        total_erros = sum(len(dados.get(k, [])) for k in
            ["erros_unidade","erros_cst","erros_credito_indevido","erros_bc_icms","erros_notas_canceladas"])
        saidas  = dados.get("vl_icms_saidas_c190", 0.0)
        debitos = dados.get("vl_tot_debitos_e110", 0.0)
        div     = abs(saidas - debitos)
        dt_ini  = dados.get("dt_ini", "")
        periodo = f"{dt_ini[:2]}/{dt_ini[4:]}" if len(dt_ini) >= 8 else ""
        erros_j = json.dumps({
            "cst":             len(dados.get("erros_cst", [])),
            "credito_indevido":len(dados.get("erros_credito_indevido", [])),
            "unidade":         len(dados.get("erros_unidade", [])),
            "bc_icms":         len(dados.get("erros_bc_icms", [])),
            "notas_canceladas":len(dados.get("erros_notas_canceladas", [])),
        })
        aid = str(uuid.uuid4())
        p = _ph()
        with _db_lock:
            conn = _get_conn()
            try:
                _exec(conn, f"""
                    INSERT INTO auditorias
                        (id,tenant_id,empresa_id,usuario_id,periodo,layout_versao,
                         total_linhas,total_erros,score,vl_icms_saidas,vl_debitos_e110,
                         divergencia_icms,erros_graves,erros_op,erros_json,status,criado_em)
                    VALUES({p},{p},{p},{p},{p},{p},{p},{p},{p},{p},{p},{p},{p},{p},{p},'concluido',{p})
                """, (aid, tenant_id, eid, usuario_id, periodo, dados.get("versao_layout",""),
                      dados.get("total_linhas", 0), total_erros, score, saidas, debitos,
                      div, eg, eo, erros_j, datetime.now().isoformat()))
                conn.commit()
            finally:
                conn.close()
        registrar_uso(tenant_id)
        log.info(f"Auditoria {aid} salva (tenant={tenant_id})")

        # Gera alertas automáticos e notificação por e-mail
        hist_recente = buscar_historico(tenant_id, cnpj, limite=3)
        # busca e-mail do admin do tenant
        try:
            with _db_lock:
                conn2 = _get_conn()
                adm = _row(conn2, f"SELECT email FROM usuarios WHERE tenant_id={_ph()} AND papel='admin' AND ativo=1 LIMIT 1", (tenant_id,))
                conn2.close()
            email_adm = adm["email"] if adm else ""
        except Exception:
            email_adm = ""

        _verificar_e_gerar_alertas(
            tenant_id, eid, nome, dados, score, eg,
            hist_recente, email_adm, periodo
        )
        return aid
    except Exception as e:
        log.error(f"Erro ao salvar auditoria: {e}")
        return None

def buscar_historico(tenant_id: str, cnpj: str, limite: int = 24) -> list[dict]:
    """Histórico SOMENTE do tenant logado — isolamento total."""
    try:
        p = _ph()
        with _db_lock:
            conn = _get_conn()
            try:
                rows = _rows(conn, f"""
                    SELECT a.periodo, a.score, a.total_erros, a.erros_graves,
                           a.divergencia_icms, a.criado_em
                    FROM auditorias a
                    JOIN empresas e ON a.empresa_id = e.id
                    WHERE a.tenant_id={p} AND e.cnpj={p}
                    ORDER BY a.criado_em DESC LIMIT {p}
                """, (tenant_id, cnpj, limite))
            finally:
                conn.close()
        return rows
    except Exception as e:
        log.error(f"Erro buscar_historico: {e}")
        return []

def listar_empresas_tenant(tenant_id: str) -> list[dict]:
    with _db_lock:
        conn = _get_conn()
        try:
            rows = _rows(conn, f"SELECT * FROM empresas WHERE tenant_id={_ph()} ORDER BY nome", (tenant_id,))
        finally:
            conn.close()
    return rows

# ══════════════════════════════════════════════════════════════════════════════
# LOG DE ACESSO — LGPD
# ══════════════════════════════════════════════════════════════════════════════

def _get_client_ip() -> str:
    """Tenta capturar o IP do cliente via headers do Streamlit."""
    try:
        headers = st.context.headers
        for h in ("x-forwarded-for", "x-real-ip", "remote-addr"):
            val = headers.get(h, "")
            if val:
                return val.split(",")[0].strip()
    except Exception:
        pass
    return "desconhecido"

def registrar_log(tenant_id: str, usuario_id: str, email: str, acao: str, detalhe: str = ""):
    """Grava evento auditável no banco, incluindo IP do cliente."""
    try:
        ip = _get_client_ip()
        detalhe_completo = f"{detalhe} [IP:{ip}]".strip() if ip != "desconhecido" else detalhe
        with _db_lock:
            conn = _get_conn()
            try:
                p = _ph()
                _exec(conn, f"""
                    INSERT INTO log_acesso(id,tenant_id,usuario_id,usuario_email,acao,detalhe,criado_em)
                    VALUES({p},{p},{p},{p},{p},{p},{p})
                """, (str(uuid.uuid4()), tenant_id, usuario_id, email, acao, detalhe_completo, datetime.now().isoformat()))
                conn.commit()
            finally:
                conn.close()
    except Exception as e:
        log.warning(f"Falha ao registrar log: {e}")

def buscar_log_acesso(tenant_id: str, limite: int = 100) -> list[dict]:
    try:
        with _db_lock:
            conn = _get_conn()
            try:
                rows = _rows(conn, f"""
                    SELECT usuario_email, acao, detalhe, criado_em
                    FROM log_acesso WHERE tenant_id={_ph()}
                    ORDER BY criado_em DESC LIMIT {_ph()}
                """, (tenant_id, limite))
            finally:
                conn.close()
        return rows
    except Exception as e:
        log.error(f"buscar_log_acesso: {e}")
        return []

# ══════════════════════════════════════════════════════════════════════════════
# ALERTAS IN-APP E NOTIFICAÇÃO POR E-MAIL
# ══════════════════════════════════════════════════════════════════════════════

def criar_alerta(tenant_id: str, empresa_id: str, tipo: str, mensagem: str):
    """Registra alerta no banco; ignora duplicatas do mesmo tipo/empresa/dia."""
    try:
        with _db_lock:
            conn = _get_conn()
            try:
                p = _ph()
                # Deduplicação: evita múltiplos alertas idênticos no mesmo dia
                hoje = datetime.now().strftime("%Y-%m-%d")
                existente = _row(conn, f"""
                    SELECT id FROM alertas
                    WHERE tenant_id={p} AND empresa_id={p} AND tipo={p}
                      AND mensagem={p} AND criado_em LIKE {p}
                    LIMIT 1
                """, (tenant_id, empresa_id, tipo, mensagem, f"{hoje}%"))
                if existente:
                    log.debug(f"criar_alerta: duplicata ignorada ({tipo} / {empresa_id})")
                    return
                _exec(conn, f"""
                    INSERT INTO alertas(id,tenant_id,empresa_id,tipo,mensagem,criado_em)
                    VALUES({p},{p},{p},{p},{p},{p})
                """, (str(uuid.uuid4()), tenant_id, empresa_id, tipo, mensagem, datetime.now().isoformat()))
                conn.commit()
            finally:
                conn.close()
    except Exception as e:
        log.warning(f"criar_alerta: {e}")

def buscar_alertas(tenant_id: str, apenas_nao_lidos: bool = True) -> list[dict]:
    try:
        filtro = "AND lido=0" if apenas_nao_lidos else ""
        with _db_lock:
            conn = _get_conn()
            try:
                rows = _rows(conn, f"""
                    SELECT a.id, a.tipo, a.mensagem, a.lido, a.criado_em,
                           e.nome as empresa_nome
                    FROM alertas a LEFT JOIN empresas e ON a.empresa_id = e.id
                    WHERE a.tenant_id={_ph()} {filtro}
                    ORDER BY a.criado_em DESC LIMIT 50
                """, (tenant_id,))
            finally:
                conn.close()
        return rows
    except Exception as e:
        log.error(f"buscar_alertas: {e}")
        return []

def marcar_alertas_lidos(tenant_id: str):
    try:
        with _db_lock:
            conn = _get_conn()
            try:
                _exec(conn, f"UPDATE alertas SET lido=1 WHERE tenant_id={_ph()}", (tenant_id,))
                conn.commit()
            finally:
                conn.close()
    except Exception as e:
        log.warning(f"marcar_alertas_lidos: {e}")

def enviar_email(destinatario: str, assunto: str, corpo_html: str) -> bool:
    """Envia e-mail via SMTP configurado em variáveis de ambiente."""
    if not NOTIF_ENABLED:
        log.info(f"E-mail não configurado. Destino: {destinatario} | Assunto: {assunto}")
        return False
    try:
        msg = MIMEMultipart("alternative")
        msg["Subject"] = assunto
        msg["From"]    = EMAIL_FROM
        msg["To"]      = destinatario
        msg.attach(MIMEText(corpo_html, "html"))
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT) as s:
            s.starttls()
            s.login(SMTP_USER, SMTP_PASS)
            s.send_message(msg)
        log.info(f"E-mail enviado: {destinatario} | {assunto}")
        return True
    except Exception as e:
        log.error(f"Falha ao enviar e-mail: {e}")
        return False

def _html_alerta(empresa: str, score: int, erros_graves: int, divergencia: float, periodo: str) -> str:
    cor = "#16a34a" if score >= 75 else "#d97706" if score >= 60 else "#dc2626"
    return f"""
    <div style="font-family:sans-serif;max-width:600px;margin:0 auto">
      <h2 style="color:#1e293b">Auditax 360º — Resultado de Auditoria</h2>
      <p><b>Empresa:</b> {empresa} &nbsp;|&nbsp; <b>Período:</b> {periodo}</p>
      <div style="background:{cor};color:#fff;border-radius:8px;padding:16px;text-align:center;margin:16px 0">
        <span style="font-size:32px;font-weight:700">{score}/100</span><br>
        <span>Score Fiscal</span>
      </div>
      <table style="width:100%;border-collapse:collapse">
        <tr><td style="padding:8px;border-bottom:1px solid #e2e8f0">Erros Graves</td>
            <td style="padding:8px;border-bottom:1px solid #e2e8f0;text-align:right;color:{'#dc2626' if erros_graves>0 else '#16a34a'}">{erros_graves}</td></tr>
        <tr><td style="padding:8px">Divergência ICMS</td>
            <td style="padding:8px;text-align:right;color:{'#dc2626' if divergencia>2 else '#16a34a'}">R$ {divergencia:,.2f}</td></tr>
      </table>
      <p style="color:#64748b;font-size:12px;margin-top:24px">Auditax 360º Enterprise — auditoria fiscal automatizada</p>
    </div>"""

def _verificar_e_gerar_alertas(tenant_id: str, empresa_id: str, empresa_nome: str,
                                 dados: dict, score: int, eg: int, hist: list,
                                 email_admin: str, periodo: str):
    """Gera alertas in-app e envia e-mail quando há degradação ou erros graves."""
    alertas_gerados = []

    # Alerta: erros graves novos
    if eg > 0:
        msg = f"{empresa_nome} — {eg} erro(s) grave(s) no período {periodo}"
        criar_alerta(tenant_id, empresa_id, "erro_grave", msg)
        alertas_gerados.append(msg)

    # Alerta: score abaixo de 60
    if score < 60:
        msg = f"{empresa_nome} — Score {score}/100 está em zona de Alto Risco ({periodo})"
        criar_alerta(tenant_id, empresa_id, "score_critico", msg)
        alertas_gerados.append(msg)

    # Alerta: tendência de queda (compara com período anterior)
    if len(hist) >= 2:
        score_anterior = hist[1].get("score", score)  # hist[0] é o atual
        queda = score_anterior - score
        if queda >= 10:
            msg = f"{empresa_nome} — Score caiu {queda} pontos vs período anterior"
            criar_alerta(tenant_id, empresa_id, "queda_score", msg)
            alertas_gerados.append(msg)

    # Alerta: divergência ICMS acima de R$ 1.000
    div = abs(dados.get("vl_icms_saidas_c190", 0) - dados.get("vl_tot_debitos_e110", 0))
    if div > 1000:
        msg = f"{empresa_nome} — Divergência ICMS de R$ {div:,.2f} no período {periodo}"
        criar_alerta(tenant_id, empresa_id, "divergencia_icms", msg)
        alertas_gerados.append(msg)

    # Envia e-mail se há alertas e SMTP configurado
    if alertas_gerados and email_admin:
        corpo = _html_alerta(empresa_nome, score, eg, div, periodo)
        enviar_email(email_admin, f"[Auditax] Alerta Fiscal — {empresa_nome}", corpo)

# ══════════════════════════════════════════════════════════════════════════════
# COMPARATIVO MULTIEMPRESA
# ══════════════════════════════════════════════════════════════════════════════

def buscar_comparativo_tenant(tenant_id: str) -> list[dict]:
    """Retorna última auditoria de cada empresa do tenant para comparativo."""
    try:
        with _db_lock:
            conn = _get_conn()
            try:
                rows = _rows(conn, f"""
                    SELECT e.nome, e.cnpj, e.uf,
                           a.periodo, a.score, a.total_erros, a.erros_graves,
                           a.divergencia_icms, a.vl_icms_saidas, a.criado_em
                    FROM empresas e
                    JOIN auditorias a ON a.empresa_id = e.id
                    WHERE e.tenant_id = {_ph()}
                      AND a.criado_em = (
                          SELECT MAX(a2.criado_em) FROM auditorias a2
                          WHERE a2.empresa_id = e.id AND a2.tenant_id = {_ph()}
                      )
                    ORDER BY a.score ASC
                """, (tenant_id, tenant_id))
            finally:
                conn.close()
        return rows
    except Exception as e:
        log.error(f"buscar_comparativo_tenant: {e}")
        return []

# ══════════════════════════════════════════════════════════════════════════════
# BASE LEGAL — fundamento normativo por tipo de erro
# ══════════════════════════════════════════════════════════════════════════════

BASE_LEGAL: dict[str, dict] = {
    "erros_bc_icms": {
        "titulo": "Base de Cálculo Zerada com ICMS Destacado",
        "norma": "Art. 13, LC 87/1996 — a BC do ICMS é o valor da operação; BC zerada com imposto destacado indica lançamento incorreto.",
        "risco": "Alto",
    },
    "erros_credito_indevido": {
        "titulo": "Crédito de ICMS Indevido",
        "norma": "Art. 20, LC 87/1996 — o crédito só é admitido para mercadorias destinadas à comercialização, industrialização ou uso/consumo autorizado.",
        "risco": "Alto",
    },
    "erros_notas_canceladas": {
        "titulo": "Nota Fiscal Cancelada com Valor Lançado",
        "norma": "Art. 7º, Ajuste SINIEF 07/2005 — NF-e cancelada não pode gerar crédito/débito de ICMS.",
        "risco": "Alto",
    },
    "erros_aliquota_invalida": {
        "titulo": "Alíquota de ICMS Fora do Padrão",
        "norma": "Art. 155, §2º, IV, CF/88 e Resoluções do Senado — alíquotas interestaduais fixadas em 4%, 7% ou 12%; internas definidas por cada UF.",
        "risco": "Alto",
    },
    "erros_d100": {
        "titulo": "CT-e de Saída sem Registro D190",
        "norma": "Guia Prático EFD-ICMS/IPI v3.1.7 — CT-e de saída tributado exige D190 correspondente na apuração.",
        "risco": "Alto",
    },
    "erros_cst": {
        "titulo": "Item Tributado (CST 00) sem ICMS Destacado",
        "norma": "Tabela CST ICMS (Ajuste SINIEF 03/94) — CST 00 implica operação tributada integralmente; ausência de ICMS configura subfaturamento.",
        "risco": "Médio",
    },
    "erros_unidade": {
        "titulo": "Divergência de Unidade de Medida",
        "norma": "Registro 0200 — IN RFB 2.004/2021; a unidade declarada no inventário deve coincidir com a dos documentos fiscais.",
        "risco": "Médio",
    },
    "erros_sequencia_nf": {
        "titulo": "Salto na Numeração de NF-e",
        "norma": "Art. 2º, Ajuste SINIEF 07/2005 — a numeração das NF-e deve ser sequencial e contínua por série.",
        "risco": "Médio",
    },
    "erros_nfe_duplicada": {
        "titulo": "NF-e com Chave de Acesso Duplicada",
        "norma": "Art. 9º, Ajuste SINIEF 07/2005 — cada NF-e tem chave única de 44 dígitos; duplicidade indica relançamento indevido.",
        "risco": "Alto",
    },
    "erros_icms_st": {
        "titulo": "ICMS-ST sem Base de Cálculo ou Valor Preenchido",
        "norma": "Art. 6º, LC 87/1996 — a substituição tributária exige BC-ST calculada pela MVA ou pauta definida pelo Estado.",
        "risco": "Alto",
    },
    "erros_difal": {
        "titulo": "DIFAL — Alíquota Interestadual Suspeita",
        "norma": "EC 87/2015 e LC 190/2022 — operações B2C interestaduais exigem recolhimento do DIFAL ao Estado de destino.",
        "risco": "Alto",
    },
    "divergencia_bloco_e": {
        "titulo": "Divergência entre Saídas e Débitos Declarados (Bloco E)",
        "norma": "Art. 50, Conv. ICMS 142/2018 / Guia Prático EFD — o E110 deve refletir exatamente a soma dos débitos apurados em C190 e D190.",
        "risco": "Alto",
    },
}

def get_base_legal(chave: str) -> str:
    """Retorna string formatada com norma e risco para exibição no app."""
    info = BASE_LEGAL.get(chave)
    if not info:
        return ""
    risco_cor = {"Alto": "🔴", "Médio": "🟡", "Baixo": "🟢"}.get(info["risco"], "⚪")
    return f"{risco_cor} **Risco {info['risco']}** | 📖 *{info['norma']}*"

# ══════════════════════════════════════════════════════════════════════════════
# SCORE
# ══════════════════════════════════════════════════════════════════════════════

def calcular_score(dados: dict) -> tuple[int, int, int]:
    eg = (len(dados.get("erros_bc_icms", [])) +
          len(dados.get("erros_credito_indevido", [])) +
          len(dados.get("erros_notas_canceladas", [])) +
          len(dados.get("erros_aliquota_invalida", [])) +
          len(dados.get("erros_d100", [])))           # CT-e sem D190
    eo = (len(dados.get("erros_unidade", [])) +
          len(dados.get("erros_cst", [])) +
          len(dados.get("erros_sequencia_nf", [])))
    # Saídas = NF-e (C190) + CT-e (D190)
    saidas_nfe = dados.get("vl_icms_saidas_c190", 0.0)
    saidas_cte = dados.get("vl_icms_servicos_d190", 0.0)
    saidas = saidas_nfe + saidas_cte
    div = abs(saidas - dados.get("vl_tot_debitos_e110", 0.0))
    perc = (div / saidas) if saidas > 0 else 0
    score = 100 - (eg * 4) - (eo * 1) - (perc * 30)
    return max(0, round(score)), eg, eo

def _rating_letra(pontos: int) -> str:
    """Converte pontuação 0-100 em rating A-F com emoji."""
    if pontos >= 90: return "🟢 A"
    if pontos >= 75: return "🟡 B"
    if pontos >= 60: return "🟠 C"
    if pontos >= 45: return "🔴 D"
    if pontos >= 25: return "🔴 E"
    return "⛔ F"

def calcular_rating_blocos(dados: dict) -> dict[str, dict]:
    """
    Calcula rating A-F para cada bloco do SPED.
    Retorna dict com chave = bloco, valor = {rating, pontos, erros, descricao}
    """
    blocos = {}

    # Bloco C — NF-e
    erros_c = (len(dados.get("erros_nfe_duplicada", [])) +
               len(dados.get("erros_notas_canceladas", [])) +
               len(dados.get("erros_bc_icms", [])) +
               len(dados.get("erros_credito_indevido", [])))
    total_nfe = max(len(dados.get("notas_sped", {})), 1)
    pontos_c = max(0, round(100 - (erros_c / total_nfe) * 100 - len(dados.get("erros_nfe_duplicada", [])) * 5))
    blocos["C"] = {"bloco": "Bloco C", "descricao": "NF-e (Notas Fiscais)", "pontos": min(pontos_c, 100),
                   "rating": _rating_letra(min(pontos_c, 100)), "erros": erros_c}

    # Bloco D — CT-e
    erros_d = len(dados.get("erros_d100", []))
    total_cte = max(dados.get("total_cte", 0), 1)
    pontos_d = max(0, round(100 - (erros_d / total_cte) * 100))
    blocos["D"] = {"bloco": "Bloco D", "descricao": "CT-e (Fretes)", "pontos": min(pontos_d, 100),
                   "rating": _rating_letra(min(pontos_d, 100)), "erros": erros_d}

    # Bloco E — Apuração ICMS
    saidas = dados.get("vl_icms_saidas_c190", 0.0) + dados.get("vl_icms_servicos_d190", 0.0)
    debitos = dados.get("vl_tot_debitos_e110", 0.0)
    div_e = abs(saidas - debitos)
    perc_e = (div_e / saidas * 100) if saidas > 0 else 0
    pontos_e = max(0, round(100 - perc_e * 3))
    blocos["E"] = {"bloco": "Bloco E", "descricao": "Apuração ICMS", "pontos": min(pontos_e, 100),
                   "rating": _rating_letra(min(pontos_e, 100)), "erros": 1 if div_e > 2 else 0}

    # Bloco G — CIAP
    tem_ciap = bool(dados.get("g110_ciap"))
    pontos_g = 85 if tem_ciap else 100  # sem CIAP não é erro, mas sem dados = neutro
    blocos["G"] = {"bloco": "Bloco G", "descricao": "CIAP (Ativo Imobilizado)", "pontos": pontos_g,
                   "rating": _rating_letra(pontos_g), "erros": 0}

    # Bloco H — Inventário
    tem_h = bool(dados.get("h010_inventario"))
    pontos_h = 90 if tem_h else 70  # inventário presente é bom sinal
    blocos["H"] = {"bloco": "Bloco H", "descricao": "Inventário (Estoque)", "pontos": pontos_h,
                   "rating": _rating_letra(pontos_h), "erros": 0}

    # Cadastros — 0200/0400
    erros_cad = len(dados.get("prods_uso", set()) - dados.get("reg_0200", set()))
    nats_falt  = len([n for n in dados.get("mapa_0400", {}) if n not in dados.get("reg_0400", set())])
    pontos_cad = max(0, 100 - erros_cad * 2 - nats_falt * 3)
    blocos["0"] = {"bloco": "Bloco 0", "descricao": "Cadastros (0200/0400)", "pontos": min(pontos_cad, 100),
                   "rating": _rating_letra(min(pontos_cad, 100)), "erros": erros_cad + nats_falt}

    return blocos

# ══════════════════════════════════════════════════════════════════════════════
# BLOQUEADOR 3 — PROCESSAMENTO ASSÍNCRONO
# ══════════════════════════════════════════════════════════════════════════════

# Fila global por job_id
# IMPORTANTE: st.cache_resource é a forma oficial do Streamlit para singletons
# que sobrevivem a reruns E a recarregamentos de módulo. globals() não é suficiente.
@st.cache_resource
def _get_job_store():
    """Retorna o dict e lock compartilhados entre todos os reruns."""
    return {}, threading.Lock()

# Referências locais para conveniência (apontam para os objetos singleton)
_job_results, _job_lock = _get_job_store()

def _processar_em_thread(job_id: str, conteudo: str):
    """Roda em thread separada; escreve resultado em _job_results."""
    _jr, _jl = _get_job_store()   # sempre pega do singleton
    try:
        with _jl:
            _jr[job_id] = {"status": "processando", "progresso": 0, "dados": None, "erro": None}

        linhas_iter = conteudo.split("\n")
        total = len(linhas_iter)
        dados = {
            # campos originais
            "c190": [], "c190_lista": [], "reg_0200": set(), "reg_0400": set(), "prods_uso": set(),
            "mapa_0400": {}, "mapa_ncm": {}, "unidades_produto": {}, "erros_unidade": [],
            "erros_cst": [], "erros_credito_indevido": [], "erros_bc_icms": [],
            "erros_cfop_invalido": [], "erros_notas_canceladas": [], "notas_sped": {},
            "total_linhas": 0, "versao_layout": "", "dt_ini": "", "dt_fin": "",
            "nome_empresa": "", "cnpj": "", "ie": "", "uf_origem": "",
            "vl_icms_saidas_c190": 0.0, "vl_tot_debitos_e110": 0.0,
            # novos — registros adicionais
            "e111_ajustes": [], "vl_ajustes_e111": 0.0,
            "e116_obrigacoes": [], "vl_total_e116": 0.0,
            "vl_debito_liquido_bloco_e": 0.0,
            "g110_ciap": [], "vl_credito_ciap": 0.0,
            "h010_inventario": {}, "vl_total_inventario": 0.0,
            "h020_detalhe": [],
            "c110_info": {},
            # novos — validações
            "erros_nfe_duplicada": [],
            "erros_sequencia_nf": [],
            "erros_difal": [],
            "erros_icms_st": [],
            "erros_aliquota_invalida": [],
            "_numeros_nf": [],
            "_numeros_saida": {},   # {serie: [nums]} — apenas saídas emissão própria
            "_cst_st_count": 0,
            # cruzamento ERP
            "c100_por_chave": {},
            "resultado_cruzamento_erp": None,
            "mapa_cest": {},          # COD_ITEM → CEST (0200 campo 13 — Guia 3.2.3)
            # Bloco D — CT-e (Conhecimento de Transporte Eletrônico)
            "d100_cte": [],            # lista de CT-e lidos
            "d190_icms": [],           # totais ICMS por CT-e
            "vl_icms_servicos_d190": 0.0,  # soma ICMS saídas (frete próprio)
            "vl_doc_servicos_d100": 0.0,   # soma VL_DOC dos CT-e (base para CBS frete)
            "total_cte": 0,
            "erros_d100": [],          # CT-e com ICMS mas sem D190
        }

        validador_reforma = ValidadorReforma2026(regime_tributario=REGIME_LUCRO_REAL) if HAS_REFORMA else None

        for i, linha in enumerate(linhas_iter):
            if i % 5000 == 0:
                prog = min(int(i / total * 95), 95)
                with _jl:
                    _jr[job_id]["progresso"] = prog

            dados["total_linhas"] += 1
            parts = linha.split("|")
            if len(parts) < 2:
                continue
            reg = parts[1]

            if reg == "0000":
                dados["versao_layout"] = parts[2] if len(parts) > 2 else "??"
                dados["dt_ini"]        = parts[4] if len(parts) > 4 else ""
                dados["dt_fin"]        = parts[5] if len(parts) > 5 else ""
                dados["nome_empresa"]  = parts[6] if len(parts) > 6 else ""
                dados["cnpj"]          = parts[7] if len(parts) > 7 else ""
                dados["uf_origem"]     = parts[9] if len(parts) > 9 else ""
                dados["ie"]            = parts[10] if len(parts) > 10 else ""
                if HAS_REFORMA and validador_reforma:
                    validador_reforma.validar_registro_0000(i, parts)

            elif reg == "C100":
                if len(parts) > 13:
                    ind_oper = parts[2] if len(parts) > 2 else ""  # 0=entrada, 1=saída
                    ind_emit = parts[3] if len(parts) > 3 else ""  # 0=própria, 1=terceiros
                    # parts[4] = COD_PART (código do participante) — NÃO é UF
                    cod_mod  = parts[5] if len(parts) > 5 else ""
                    cod_sit  = parts[6] if len(parts) > 6 else ""
                    ser_nf   = parts[7] if len(parts) > 7 else ""
                    num_nf   = re.sub(r"\D", "", parts[8]) if len(parts) > 8 else ""
                    chv_nfe  = re.sub(r"\D", "", parts[9]) if len(parts) > 9 else ""
                    dt_doc   = parts[10] if len(parts) > 10 else ""
                    vl_doc   = _tf(parts[12]) if len(parts) > 12 else 0.0
                    # Índices conforme Guia Prático EFD-ICMS/IPI v3.2.3:
                    # campo 22=VL_ICMS, 23=VL_BC_ICMS_ST, 24=VL_ICMS_ST, 25=VL_IPI, 26=VL_PIS, 27=VL_COFINS
                    vl_icms  = _tf(parts[22]) if len(parts) > 22 else 0.0
                    vl_ipi   = _tf(parts[25]) if len(parts) > 25 else 0.0
                    vl_pis   = _tf(parts[26]) if len(parts) > 26 else 0.0
                    vl_cofins= _tf(parts[27]) if len(parts) > 27 else 0.0

                    # ── CNPJ extraído corretamente da chave NF-e (posições 6-20) ──
                    # Layout chave 44 dígitos: [0:2]=cUF [2:6]=AAMM [6:20]=CNPJ [20:24]=mod
                    cnpj_emit = chv_nfe[6:20] if len(chv_nfe) == 44 else ""
                    # UF de origem deduzida do cUF da chave (posições 0:2)
                    CUF_TO_UF = {
                        "12":"AC","27":"AL","16":"AP","13":"AM","29":"BA","23":"CE","53":"DF",
                        "32":"ES","52":"GO","21":"MA","51":"MT","50":"MS","31":"MG","15":"PA",
                        "25":"PB","41":"PR","26":"PE","22":"PI","33":"RJ","24":"RN","43":"RS",
                        "11":"RO","14":"RR","42":"SC","35":"SP","28":"SE","17":"TO",
                    }
                    uf_emit = CUF_TO_UF.get(chv_nfe[:2], "") if len(chv_nfe) == 44 else ""

                    # Chave composta para cruzamento ERP — número + CNPJ emitente
                    chave_composta = f"{num_nf}|{cnpj_emit}" if num_nf and cnpj_emit else ""

                    tipo_op = "ENTRADA" if ind_oper == "0" else "SAIDA"

                    if chv_nfe and len(chv_nfe) == 44 and cod_sit == "00":
                        if chv_nfe in dados["notas_sped"]:
                            dados["erros_nfe_duplicada"].append({
                                "Chave": chv_nfe, "Nota": num_nf,
                                "Erro": "Chave NF-e duplicada no SPED"
                            })
                        else:
                            dados["notas_sped"][chv_nfe] = {
                                "vNF": vl_doc, "vICMS": vl_icms,
                                "vPIS": vl_pis, "vCOFINS": vl_cofins, "vIPI": vl_ipi,
                                "num": num_nf, "serie": ser_nf,
                                "cnpj_emit": cnpj_emit, "uf_emit": uf_emit,
                                "ind_emit": ind_emit, "tipo_op": tipo_op,
                                "dt_doc": dt_doc, "chave_composta": chave_composta,
                            }
                            # Armazena para cruzamento ERP
                            if chave_composta:
                                dados["c100_por_chave"][chave_composta] = {
                                    "CHAVE_COMPOSTA": chave_composta,
                                    "NUMERO_NOTA": num_nf,
                                    "CNPJ_FORNECEDOR": cnpj_emit,
                                    "CHAVE_NFE": chv_nfe,
                                    "SERIE": ser_nf,
                                    "DATA_EMISSAO": dt_doc,
                                    "VALOR_TOTAL": vl_doc,
                                    "VALOR_ICMS": vl_icms,
                                    "VALOR_PIS": vl_pis,
                                    "VALOR_COFINS": vl_cofins,
                                    "VALOR_IPI": vl_ipi,
                                    "TIPO_OPERACAO": tipo_op,
                                    "UF_EMIT": uf_emit,
                                    "CNPJ_EMPRESA_SPED": dados.get("cnpj", ""),
                                }

                        if ind_emit == "0" and num_nf.isdigit():
                            dados["_numeros_nf"].append(int(num_nf))

                        # Controle de sequência: apenas saídas de emissão própria
                        if ind_oper == "1" and ind_emit == "0" and num_nf.isdigit():
                            dados["_numeros_saida"].setdefault(ser_nf, []).append(int(num_nf))

                    if cod_sit in ["02","03","04","05"] and (vl_doc > 0 or vl_icms > 0):
                        dados["erros_notas_canceladas"].append({
                            "Nota": num_nf, "Situação": cod_sit,
                            "Valor Indevido": max(vl_doc, vl_icms), "Erro": "Cancelada com valor"
                        })

            elif reg == "C110":
                # Informações complementares da nota — contexto para operações especiais
                chv_ref = parts[3] if len(parts) > 3 else ""
                info_compl = parts[4] if len(parts) > 4 else ""
                if chv_ref:
                    dados["c110_info"][chv_ref] = info_compl

            elif reg == "C190":
                try:
                    cfop    = parts[3]
                    cst_icms= parts[2] if len(parts) > 2 else ""
                    valor   = _tf(parts[5])
                    icms    = _tf(parts[7])
                    bc      = _tf(parts[6])
                    dados["c190"].append({"CFOP": cfop, "CST": cst_icms, "Valor": valor, "ICMS": icms, "BC_ICMS": bc})
                    dados["c190_lista"].append({"CFOP": cfop, "Valor": valor, "ICMS": icms})
                    if cfop.startswith(("5","6","7")):
                        dados["vl_icms_saidas_c190"] += icms

                    # BC zerada com ICMS
                    if bc == 0 and icms > 0:
                        dados["erros_bc_icms"].append({
                            "Linha": i+1, "CFOP": cfop, "CST": cst_icms,
                            "BC_ICMS": bc, "ICMS": icms, "Erro": "BC zerada com ICMS destacado"
                        })

                    # Alíquota inválida — valores acima de 30% com BC > 0 são suspeitos
                    # (alíquotas válidas ICMS: 4%, 7%, 12%, 17%, 18%, 20%, 25%, 28%)
                    try:
                        aliq_raw = _tf(parts[4]) if len(parts) > 4 else 0.0
                        _ALIQ_ICMS_VALIDAS = {4.0, 7.0, 12.0, 17.0, 18.0, 19.0, 20.0, 25.0, 28.0}
                        if aliq_raw > 0 and bc > 0:
                            # Verifica se a alíquota calculada bate com o campo informado
                            aliq_calc = round(icms / bc * 100, 2) if bc > 0 else 0.0
                            if aliq_raw > 30:
                                dados["erros_aliquota_invalida"].append({
                                    "Linha": i+1, "CFOP": cfop, "CST": cst_icms,
                                    "Alíquota Informada": f"{aliq_raw}%",
                                    "BC": bc, "ICMS": icms,
                                    "Erro": f"Alíquota {aliq_raw}% acima de 30% — fora do padrão ICMS"
                                })
                            elif aliq_raw not in _ALIQ_ICMS_VALIDAS and abs(aliq_raw - aliq_calc) > 0.5:
                                dados["erros_aliquota_invalida"].append({
                                    "Linha": i+1, "CFOP": cfop, "CST": cst_icms,
                                    "Alíquota Informada": f"{aliq_raw}%",
                                    "Alíquota Calculada": f"{aliq_calc:.1f}%",
                                    "BC": bc, "ICMS": icms,
                                    "Erro": f"Divergência entre alíquota informada ({aliq_raw}%) e calculada ({aliq_calc:.1f}%)"
                                })
                    except Exception:
                        pass

                    # DIFAL — saída interestadual para não-contribuinte (CFOP 6xxx)
                    # Alíquotas interestaduais válidas: 4% (importados), 7% (Sul/Sudeste→Norte/NE/CO), 12% (demais)
                    _ALIQ_INTER_VALIDAS = {4.0, 7.0, 12.0}
                    if cfop.startswith("6") and icms > 0:
                        uf_origem = dados.get("uf_origem","")
                        aliq_devida = ALIQ_INTERESTADUAL.get(uf_origem, 12.0)
                        # verifica se alíquota aplicada é coerente com a UF de origem
                        if bc > 0:
                            aliq_aplicada = round(icms / bc * 100, 2)
                            # Tolerância de 0.5% para arredondamentos; alíquota deve estar nas válidas
                            if aliq_aplicada not in _ALIQ_INTER_VALIDAS and abs(aliq_aplicada - aliq_devida) > 0.5:
                                dados["erros_difal"].append({
                                    "Linha": i+1, "CFOP": cfop,
                                    "UF Origem": uf_origem,
                                    "Alíq. Aplicada": f"{aliq_aplicada:.1f}%",
                                    "Alíq. Devida UF": f"{aliq_devida:.1f}%",
                                    "Erro": "Alíquota interestadual suspeita"
                                })

                    # ICMS-ST — CST que exige ST mas sem BC_ST informado
                    cst2 = cst_icms[-2:] if len(cst_icms) >= 2 else cst_icms
                    if cst2 in CST_COM_ST:
                        dados["_cst_st_count"] += 1

                except Exception as e:
                    log.warning(f"C190 linha {i+1}: {e}")

            elif reg == "E110":
                if len(parts) > 2:
                    dados["vl_tot_debitos_e110"] += _tf(parts[2])

            elif reg == "E111":
                # Ajustes de apuração ICMS — necessário para cruzamento correto do Bloco E
                # CORREÇÃO: E111 pode ter ajustes a DÉBITO (cod começando com prefixo MG04/SP04/etc)
                # ou a CRÉDITO. Aqui acumulamos separadamente para o cálculo do débito líquido.
                try:
                    cod_aj  = parts[2] if len(parts) > 2 else ""
                    vl_aj   = _tf(parts[4]) if len(parts) > 4 else 0.0
                    descr   = parts[3] if len(parts) > 3 else ""
                    if cod_aj:
                        # Padrão Sefaz: código com dígito 1-5 na posição 4 = débito; 6-9 = crédito
                        # Heurística simplificada: acumula tudo em vl_ajustes_e111 (valor líquido)
                        # e marca o tipo no registro para exibição
                        tipo_aj = "débito" if cod_aj[3:4] in "12345" else "crédito"
                        dados["e111_ajustes"].append({
                            "Cód. Ajuste": cod_aj, "Tipo": tipo_aj,
                            "Descrição": descr, "Valor": vl_aj
                        })
                        # Ajustes a crédito reduzem o débito; a débito aumentam
                        if tipo_aj == "crédito":
                            dados["vl_ajustes_e111"] += vl_aj
                        else:
                            dados["vl_ajustes_e111"] -= vl_aj
                except Exception as e:
                    log.warning(f"E111 linha {i+1}: {e}")

            elif reg == "E116":
                # Obrigações a recolher — DARE/GNRE
                try:
                    cod_or  = parts[2] if len(parts) > 2 else ""
                    vl_or   = _tf(parts[3]) if len(parts) > 3 else 0.0
                    dt_vcto = parts[4] if len(parts) > 4 else ""
                    cod_rec = parts[5] if len(parts) > 5 else ""
                    if vl_or > 0:
                        dados["e116_obrigacoes"].append({
                            "Cód. Obrigação": cod_or, "Valor": vl_or,
                            "Vencimento": dt_vcto, "Cód. Recolhimento": cod_rec
                        })
                        dados["vl_total_e116"] += vl_or
                except Exception as e:
                    log.warning(f"E116 linha {i+1}: {e}")

            elif reg == "G110":
                # CIAP — crédito do ativo imobilizado
                try:
                    num_doc  = parts[2] if len(parts) > 2 else ""
                    vl_cont  = _tf(parts[4]) if len(parts) > 4 else 0.0
                    vl_icms_ciap = _tf(parts[6]) if len(parts) > 6 else 0.0
                    num_parc = parts[8] if len(parts) > 8 else ""
                    if vl_icms_ciap > 0:
                        dados["g110_ciap"].append({
                            "Doc": num_doc, "Valor Contábil": vl_cont,
                            "ICMS": vl_icms_ciap, "Nº Parcela": num_parc
                        })
                        dados["vl_credito_ciap"] += vl_icms_ciap
                except Exception as e:
                    log.warning(f"G110 linha {i+1}: {e}")

            elif reg == "H010":
                # Inventário — registro de item do estoque
                try:
                    cod_item  = parts[2] if len(parts) > 2 else ""
                    unid      = parts[3] if len(parts) > 3 else ""
                    qtd       = _tf(parts[4]) if len(parts) > 4 else 0.0
                    vl_unit   = _tf(parts[5]) if len(parts) > 5 else 0.0
                    vl_item_h = _tf(parts[6]) if len(parts) > 6 else 0.0
                    ind_prop  = parts[7] if len(parts) > 7 else ""
                    if cod_item:
                        dados["h010_inventario"][cod_item] = {
                            "Unidade": unid, "Qtd": qtd,
                            "Vl. Unit.": vl_unit, "Vl. Total": vl_item_h,
                            "Proprietário": ind_prop
                        }
                        dados["vl_total_inventario"] += vl_item_h
                except Exception as e:
                    log.warning(f"H010 linha {i+1}: {e}")

            elif reg == "H020":
                # Dados do item de inventário — informações complementares
                try:
                    cst_h   = parts[2] if len(parts) > 2 else ""
                    bc_icms_h = _tf(parts[3]) if len(parts) > 3 else 0.0
                    vl_bc   = _tf(parts[4]) if len(parts) > 4 else 0.0
                    dados["h020_detalhe"].append({
                        "CST": cst_h, "BC_ICMS": bc_icms_h, "Vl. BC": vl_bc
                    })
                except Exception as e:
                    log.warning(f"H020 linha {i+1}: {e}")

            elif reg == "D100":
                # CT-e (Conhecimento de Transporte Eletrônico — modelo 57)
                try:
                    ind_oper_d = parts[2]  if len(parts) > 2  else ""  # 0=entrada, 1=saída
                    ind_emit_d = parts[3]  if len(parts) > 3  else ""  # 0=própria, 1=terceiros
                    cod_mod_d  = parts[5]  if len(parts) > 5  else ""
                    cod_sit_d  = parts[6]  if len(parts) > 6  else ""
                    ser_d      = parts[7]  if len(parts) > 7  else ""
                    num_d      = parts[8]  if len(parts) > 8  else ""
                    chv_cte    = re.sub(r"\D","",parts[9]) if len(parts) > 9 else ""
                    dt_doc_d   = parts[10] if len(parts) > 10 else ""
                    vl_doc_d   = _tf(parts[12]) if len(parts) > 12 else 0.0
                    # Índices conforme Guia Prático EFD-ICMS/IPI v3.2.3:
                    # campo 19=VL_BC_ICMS, campo 20=VL_ICMS (não campo 22)
                    vl_icms_d  = _tf(parts[20]) if len(parts) > 20 else 0.0

                    if cod_sit_d not in ("02","03","04","05"):  # ignorar cancelados
                        dados["d100_cte"].append({
                            "Série": ser_d, "Número": num_d, "Chave CT-e": chv_cte,
                            "Data": dt_doc_d, "Valor": vl_doc_d, "ICMS": vl_icms_d,
                            "Ind. Oper.": ind_oper_d, "Ind. Emit.": ind_emit_d,
                            "Situação": cod_sit_d,
                        })
                        dados["total_cte"] += 1
                        # Saídas (IND_OPER=1) = CT-e emitidos pela empresa → base CBS frete
                        if ind_oper_d in ("1",""):
                            dados["vl_doc_servicos_d100"] += vl_doc_d
                except Exception as e:
                    log.warning(f"D100 linha {i+1}: {e}")

            elif reg == "D190":
                # Totais de ICMS por CFOP/CST do CT-e
                try:
                    cfop_d  = parts[3] if len(parts) > 3 else ""
                    cst_d   = parts[2] if len(parts) > 2 else ""
                    vl_d    = _tf(parts[5]) if len(parts) > 5 else 0.0
                    icms_d  = _tf(parts[7]) if len(parts) > 7 else 0.0
                    bc_d    = _tf(parts[6]) if len(parts) > 6 else 0.0
                    dados["d190_icms"].append({
                        "CFOP": cfop_d, "CST": cst_d, "Valor": vl_d,
                        "ICMS": icms_d, "BC_ICMS": bc_d
                    })
                    # CFOPs 6xxx = saídas interestaduais (frete emitido pela empresa)
                    # CFOPs 5xxx = saídas estaduais — ambos entram na apuração
                    if cfop_d.startswith(("5","6","7")):
                        dados["vl_icms_servicos_d190"] += icms_d
                except Exception as e:
                    log.warning(f"D190 linha {i+1}: {e}")

            elif reg == "0200":
                # Guia 3.2.3: parts[2]=COD_ITEM, parts[6]=UNID_INV, parts[8]=COD_NCM, parts[13]=CEST
                if len(parts) > 2:
                    dados["reg_0200"].add(parts[2])
                if len(parts) > 6:
                    dados["unidades_produto"][parts[2]] = parts[6]
                if len(parts) > 8:
                    dados["mapa_ncm"][parts[2]] = parts[8]
                if len(parts) > 13 and parts[13].strip():
                    dados.setdefault("mapa_cest", {})[parts[2]] = parts[13].strip()

            elif reg == "0400":
                if len(parts) > 2:
                    dados["reg_0400"].add(parts[2])

            elif reg == "C170":
                try:
                    cod_item = parts[3]
                    uni_mov  = parts[6] if len(parts) > 6 else ""
                    cfop     = parts[11] if len(parts) > 11 else ""
                    cst      = parts[10] if len(parts) > 10 else ""
                    vl_item  = _tf(parts[7])
                    # Índices conforme Guia Prático EFD-ICMS/IPI v3.2.3:
                    # campo 14=ALIQ_ICMS, campo 15=VL_ICMS
                    vl_icms  = _tf(parts[15]) if len(parts) > 15 else 0.0
                    nat      = parts[12].strip() if len(parts) > 12 else ""
                    if nat:
                        dados["mapa_0400"][nat] = cfop
                    if cod_item:
                        dados["prods_uso"].add(cod_item)

                    # Unidade divergente
                    if (cod_item in dados["unidades_produto"] and
                            dados["unidades_produto"][cod_item] != uni_mov and
                            not any(e["Produto"] == cod_item and e["Unid. Movimento (C170)"] == uni_mov
                                    for e in dados["erros_unidade"])):
                        dados["erros_unidade"].append({
                            "Linha": i+1, "Produto": cod_item,
                            "Unid. Cadastro (0200)": dados["unidades_produto"][cod_item],
                            "Unid. Movimento (C170)": uni_mov
                        })

                    # CST tributado sem ICMS
                    if cst[-2:] in ["00","10","20"] and vl_icms == 0 and vl_item > 0:
                        dados["erros_cst"].append({
                            "Linha": i+1, "Item": cod_item, "CST": cst,
                            "CFOP": cfop, "Valor": vl_item, "Erro": "Tributado s/ ICMS"
                        })

                    # Crédito indevido — CFOPs expandidos
                    if cfop in CFOP_CREDITO_INDEVIDO and vl_icms > 0:
                        dados["erros_credito_indevido"].append({
                            "Linha": i+1, "Item": cod_item, "CFOP": cfop,
                            "Valor Crédito": vl_icms, "Erro": "Crédito uso/consumo indevido"
                        })

                    # ICMS-ST sem valor de BC-ST — CST 10/30/70 sem campo ST preenchido
                    cst2 = cst[-2:] if len(cst) >= 2 else cst
                    if cst2 in {"10","30","70"}:
                        # Guia 3.2.3 C170: campo 16=VL_BC_ICMS_ST, campo 17=ALIQ_ST, campo 18=VL_ICMS_ST
                        vl_bc_st = _tf(parts[16]) if len(parts) > 16 else 0.0
                        vl_icms_st = _tf(parts[18]) if len(parts) > 18 else 0.0
                        if vl_bc_st == 0 and vl_icms_st == 0 and vl_item > 0:
                            dados["erros_icms_st"].append({
                                "Linha": i+1, "Item": cod_item, "CST": cst, "CFOP": cfop,
                                "Valor Item": vl_item, "Erro": "ST sem BC/Valor informados"
                            })

                    if HAS_REFORMA and validador_reforma:
                        item_r = RegistroC170(
                            linha=i+1, num_item=parts[2], cod_item=cod_item, descr_compl="",
                            ncm=dados["mapa_ncm"].get(cod_item,""),
                            vl_item=Decimal(str(vl_item)), vl_desc=Decimal("0"),
                            alq_cbs=Decimal("0"), alq_ibs=Decimal("0"),
                            vlr_cbs=Decimal("0"), vlr_ibs=Decimal("0"), vlr_is=Decimal("0"),
                            vlr_ipi=Decimal(str(_tf(parts[24]) if len(parts) > 24 else 0.0)),
                            cfop=cfop
                        )
                        validador_reforma.validar_registro_c170(item_r)
                except Exception as e:
                    log.warning(f"C170 linha {i+1}: {e}")

        # ── Pós-processamento ──────────────────────────────────────────────────

        # Sequência de numeração — detecta saltos por série (apenas saídas emissão própria)
        for serie, nums_serie in dados.get("_numeros_saida", {}).items():
            nums = sorted(nums_serie)
            for idx in range(1, len(nums)):
                gap = nums[idx] - nums[idx-1]
                if gap > 1:
                    dados["erros_sequencia_nf"].append({
                        "Série": serie,
                        "NF Anterior": nums[idx-1],
                        "NF Seguinte": nums[idx],
                        "Gap": gap - 1,
                        "Erro": f"{gap-1} nota(s) de saída ausente(s) na sequência"
                    })

        # ── Bloco D: validação CT-e sem D190 ──────────────────────────────────
        # CT-e de saída emissão própria deve ter D190 correspondente.
        # CORREÇÃO: a validação anterior testava se vl_d190_total==0 (todo o arquivo),
        # o que suprimia alertas quando havia QUALQUER D190 no arquivo, mesmo de outro CT-e.
        # Agora verifica se há pelo menos um D190 com ICMS > 0 no arquivo.
        # (Cruzamento individual CT-e×D190 requeriria chave que o layout não fornece diretamente.)
        tem_d190_icms = any(r["ICMS"] > 0 for r in dados["d190_icms"])
        for cte in dados["d100_cte"]:
            if cte["Ind. Oper."] == "1" and cte["ICMS"] > 0 and not tem_d190_icms:
                dados["erros_d100"].append({
                    "Número": cte["Número"], "Série": cte["Série"],
                    "ICMS CT-e": cte["ICMS"],
                    "Erro": "CT-e de saída com ICMS mas sem registro D190 no arquivo"
                })

        # ── Cruzamento E110 + E111 + D190: débito líquido total ───────────────
        dados["vl_debito_liquido_bloco_e"] = (
            dados["vl_tot_debitos_e110"]
            - dados["vl_ajustes_e111"]
        )

        if HAS_REFORMA and validador_reforma:
            dados["laudo_reforma_2026"] = validador_reforma.gerar_relatorio()
        else:
            dados["laudo_reforma_2026"] = {}

        with _jl:
            _jr[job_id] = {"status": "concluido", "progresso": 100, "dados": dados, "erro": None}
        log.info(f"Job {job_id}: processamento concluído ({dados['total_linhas']} linhas)")

    except Exception as e:
        log.error(f"Job {job_id} falhou: {e}")
        with _jl:
            _jr[job_id] = {"status": "erro", "progresso": 0, "dados": None, "erro": str(e)}

def iniciar_processamento(conteudo: str) -> str:
    """Dispara thread e retorna job_id.
    CORREÇÃO: o status inicial é escrito de forma síncrona ANTES de iniciar
    a thread, evitando race condition onde o st.rerun() ocorre antes da
    thread conseguir registrar seu próprio status (causava 'não_encontrado'
    silencioso e a tela parecia não reagir ao upload)."""
    job_id = str(uuid.uuid4())
    _jr, _jl = _get_job_store()
    with _jl:
        _jr[job_id] = {"status": "processando", "progresso": 0, "dados": None, "erro": None}
    t = threading.Thread(target=_processar_em_thread, args=(job_id, conteudo), daemon=True)
    t.start()
    return job_id

def status_job(job_id: str) -> dict:
    _jr, _jl = _get_job_store()
    with _jl:
        return _jr.get(job_id, {"status": "não_encontrado", "progresso": 0, "dados": None, "erro": None})

# ══════════════════════════════════════════════════════════════════════════════
# UTILITÁRIOS
# ══════════════════════════════════════════════════════════════════════════════

def _tf(val) -> float:
    """to_float seguro."""
    if val is None or val == "":
        return 0.0
    try:
        return float(str(val).replace(".", "").replace(",", "."))
    except (ValueError, TypeError):
        return 0.0

def get_reg(line: str):
    try:
        return line.split("|")[1]
    except Exception:
        return None

def criar_backup(linhas, motivo=""):
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    if "backups" not in st.session_state:
        st.session_state["backups"] = []
    st.session_state["backups"].append({"timestamp": ts, "motivo": motivo, "linhas": linhas.copy()})
    if len(st.session_state["backups"]) > 5:
        st.session_state["backups"] = st.session_state["backups"][-5:]

def atualizar_versao(linhas, nova="020"):
    novas, lg = [], []
    for i, l in enumerate(linhas):
        if i == 0 and l.startswith("|0000|"):
            c = l.split("|")
            if len(c) > 2 and c[2] < nova:
                old, c[2] = c[2], nova
                novas.append("|".join(c))
                lg.append(f"Layout alterado de {old} para {nova}")
            else:
                novas.append(l)
        else:
            novas.append(l)
    return novas, lg

def corrigir_quebras_linha(linhas):
    novas, lg, buf = [], [], ""
    for l in linhas:
        t = l.strip()
        if not t:
            continue
        buf = (buf + t) if buf else t
        if buf.startswith("|") and buf.endswith("|"):
            novas.append(buf + "\r\n")
            buf = ""
        elif buf.endswith("|") and not buf.startswith("|"):
            buf = "|" + buf
    if buf:
        if not buf.startswith("|"):
            buf = "|" + buf
        if not buf.endswith("|"):
            buf += "|"
        novas.append(buf + "\r\n")
    return novas, lg

def recalcular_bloco9(linhas):
    """
    Recalcula o Bloco 9 (registros de totalização) conforme layout EFD-ICMS/IPI.
    CORREÇÃO: o registro 9900 precisa contar quantas linhas 9900 existirão no arquivo,
    incluindo ele mesmo + 9990 + 9999 = len(qtd)+3 (após adicionar 9001 ao dict).
    """
    limpas = [l for l in linhas if not l.startswith("|9")]
    qtd, tot = {}, 0
    for l in limpas:
        r = get_reg(l)
        if r:
            qtd[r] = qtd.get(r, 0) + 1
            tot += 1
    # Adiciona 9001 ao dict antes de calcular 9900
    qtd["9001"] = 1
    # Número de linhas 9900: um por registro + 9900 (si mesmo) + 9990 + 9999
    n_linhas_9900 = len(qtd) + 3   # +3 = 9900, 9990, 9999
    novas = ["|9001|0|\r\n"]
    for r in sorted(qtd):
        novas.append(f"|9900|{r}|{qtd[r]}|\r\n")
    novas.append(f"|9900|9900|{n_linhas_9900}|\r\n")
    novas.append("|9900|9990|1|\r\n")
    novas.append("|9900|9999|1|\r\n")
    novas.append(f"|9990|{len(novas)+1}|\r\n")
    novas.append(f"|9999|{tot + len(novas) + 1}|\r\n")
    return limpas + novas, ["Bloco 9 recalculado."]

# ══════════════════════════════════════════════════════════════════════════════
# EXPORTAÇÃO
# ══════════════════════════════════════════════════════════════════════════════

def gerar_excel(dados, log_execucao):
    out = io.BytesIO()
    with pd.ExcelWriter(out, engine="openpyxl") as w:
        if log_execucao:
            pd.DataFrame(log_execucao, columns=["Log"]).to_excel(w, sheet_name="Log", index=False)
        prods = list(dados.get("prods_uso", set()) - dados.get("reg_0200", set()))
        if prods:
            pd.DataFrame({"Cód": prods, "Descrição": [f"PROD {p}" for p in prods],
                          "Unidade": ["UN"]*len(prods), "Tipo": ["00"]*len(prods),
                          "NCM": ["00000000"]*len(prods), "Alíq. ICMS": [""]*len(prods)}
                         ).to_excel(w, sheet_name="Falta_0200", index=False)
        nats = [n for n in dados.get("mapa_0400", {}) if n not in dados.get("reg_0400", set())]
        if nats:
            pd.DataFrame([{"Cód": n, "Descrição": get_cfop_descricao(dados["mapa_0400"][n])} for n in nats]
                         ).to_excel(w, sheet_name="Falta_0400", index=False)
        if dados.get("c190_lista"):
            pd.DataFrame(dados["c190_lista"]).to_excel(w, sheet_name="C190", index=False)
        for nome_aba, chave in [("Erros_CST","erros_cst"), ("Erros_Creditos","erros_credito_indevido"),
                                 ("Erros_Unidade","erros_unidade"), ("BC_Zerada","erros_bc_icms")]:
            if dados.get(chave):
                pd.DataFrame(dados[chave]).to_excel(w, sheet_name=nome_aba, index=False)
    return out.getvalue()

def _safe_pdf(text: str) -> str:
    """Sanitiza texto para fontes core do FPDF (latin-1).
    Substitui caracteres Unicode fora do range latin-1 por equivalentes ASCII."""
    _replacements = {
        "—": "-",   # em dash  —  → -
        "–": "-",   # en dash  –  → -
        "‘": "'",   # '  → '
        "’": "'",   # '  → '
        "“": '"',   # "  → "
        "”": '"',   # "  → "
        "…": "...", # …  → ...
        "°": "o",   # °  → o
        "º": "o",   # º  → o
        "ª": "a",   # ª  → a
        "™": "TM",  # ™  → TM
        "®": "(R)", # ®  → (R)
        "©": "(C)", # ©  → (C)
    }
    for src, dst in _replacements.items():
        text = text.replace(src, dst)
    # Remove qualquer outro caractere fora do latin-1
    return text.encode("latin-1", errors="replace").decode("latin-1")

def _hex_to_rgb(hex_color: str) -> tuple[int, int, int]:
    """Converte #RRGGBB em tuple (R, G, B)."""
    h = hex_color.lstrip("#")
    if len(h) != 6:
        return (30, 58, 95)  # azul padrão
    return tuple(int(h[i:i+2], 16) for i in (0, 2, 4))

def gerar_pdf(dados, logo_bytes: bytes | None = None, cor_primaria: str = "#1E3A5F"):
    if not HAS_FPDF:
        return None
    r, g, b = _hex_to_rgb(cor_primaria)
    pdf = FPDF()
    pdf.add_page()

    # ── Cabeçalho com logo (se disponível) ────────────────────────────────────
    if logo_bytes:
        try:
            import io as _io
            with tempfile.NamedTemporaryFile(delete=False, suffix=".png") as tmp_logo:
                tmp_logo.write(logo_bytes)
                tmp_logo_path = tmp_logo.name
            pdf.image(tmp_logo_path, x=10, y=10, h=18)
            os.remove(tmp_logo_path)
            pdf.ln(22)
        except Exception:
            pdf.ln(5)
    else:
        pdf.ln(5)

    # ── Faixa de título na cor primária ───────────────────────────────────────
    pdf.set_fill_color(r, g, b)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Arial", "B", 15)
    pdf.cell(0, 12, _safe_pdf("Laudo de Auditoria Fiscal - Auditax 360"), ln=True, align="C", fill=True)
    pdf.set_text_color(0, 0, 0)
    pdf.set_font("Arial", "I", 9)
    pdf.cell(0, 7, f"Gerado em {datetime.now().strftime('%d/%m/%Y %H:%M')}", ln=True, align="C")
    pdf.ln(3)

    # ── Dados da empresa ──────────────────────────────────────────────────────
    pdf.set_fill_color(r, g, b)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Arial", "B", 11)
    pdf.cell(0, 8, "  DADOS DA EMPRESA", ln=True, fill=True)
    pdf.set_text_color(0, 0, 0)
    pdf.set_font("Arial", "", 10)
    pdf.cell(0, 6, _safe_pdf(f"  Empresa : {dados.get('nome_empresa','N/A')} (UF: {dados.get('uf_origem','')})"), ln=True)
    pdf.cell(0, 6, _safe_pdf(f"  CNPJ    : {dados.get('cnpj','')}"), ln=True)
    pdf.cell(0, 6, _safe_pdf(f"  Periodo : {dados.get('dt_ini','')} a {dados.get('dt_fin','')}  |  Layout: {dados.get('versao_layout','')}"), ln=True)
    pdf.ln(3)

    # ── Score e Rating ────────────────────────────────────────────────────────
    score, eg, eo = calcular_score(dados)
    rating_blocos = calcular_rating_blocos(dados)
    pdf.set_fill_color(r, g, b)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Arial", "B", 11)
    pdf.cell(0, 8, "  SCORE FISCAL E RATING POR BLOCO", ln=True, fill=True)
    pdf.set_text_color(0, 0, 0)
    pdf.set_font("Arial", "B", 13)
    score_cor = (0, 140, 0) if score >= 75 else (200, 100, 0) if score >= 50 else (200, 0, 0)
    pdf.set_text_color(*score_cor)
    pdf.cell(0, 10, f"  Score Global: {score}/100  |  Erros Graves: {eg}  |  Operacionais: {eo}", ln=True)
    pdf.set_text_color(0, 0, 0)
    pdf.set_font("Arial", "", 10)
    for bloco_key, info in rating_blocos.items():
        emoji_map = {"A": "[ A ]", "B": "[ B ]", "C": "[ C ]", "D": "[ D ]", "E": "[ E ]", "F": "[ F ]"}
        letra = info["rating"].split()[-1] if info["rating"] else "?"
        sufixo = f"  {info['erros']} ocorrencia(s)" if info["erros"] > 0 else "  Sem erros"
        pdf.cell(0, 6, _safe_pdf(f"  {info['bloco']} - {info['descricao']}: {letra}{sufixo}"), ln=True)
    pdf.ln(3)

    # ── Cruzamento Bloco E ────────────────────────────────────────────────────
    saidas  = dados.get("vl_icms_saidas_c190", 0.0) + dados.get("vl_icms_servicos_d190", 0.0)
    debitos = dados.get("vl_tot_debitos_e110", 0.0)
    diff    = abs(saidas - debitos)
    pdf.set_fill_color(r, g, b)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Arial", "B", 11)
    pdf.cell(0, 8, "  CRUZAMENTO BLOCO E — APURACAO ICMS", ln=True, fill=True)
    pdf.set_text_color(0, 0, 0)
    pdf.set_font("Arial", "", 10)
    pdf.cell(0, 6, f"  ICMS Saidas NF-e (C190): R$ {dados.get('vl_icms_saidas_c190',0):,.2f}", ln=True)
    pdf.cell(0, 6, f"  ICMS Fretes CT-e (D190): R$ {dados.get('vl_icms_servicos_d190',0):,.2f}", ln=True)
    pdf.cell(0, 6, f"  Total Saidas:            R$ {saidas:,.2f}", ln=True)
    pdf.cell(0, 6, f"  Debitos E110:            R$ {debitos:,.2f}", ln=True)
    if diff > 2:
        pdf.set_text_color(200, 0, 0)
        pdf.set_font("Arial", "B", 10)
        pdf.cell(0, 7, f"  DIVERGENCIA DETECTADA: R$ {diff:,.2f}", ln=True)
        bl = BASE_LEGAL.get("divergencia_bloco_e", {})
        if bl:
            pdf.set_font("Arial", "I", 8)
            pdf.cell(0, 5, _safe_pdf(f"  Base legal: {bl['norma']}"), ln=True)
    else:
        pdf.set_text_color(0, 140, 0)
        pdf.cell(0, 7, "  APURACAO VALIDADA: sem divergencias.", ln=True)
    pdf.set_text_color(0, 0, 0)
    pdf.ln(3)

    # ── Erros identificados com base legal ───────────────────────────────────
    erros_pdf = [
        ("erros_bc_icms",         "BC Zerada com ICMS"),
        ("erros_credito_indevido", "Credito Indevido"),
        ("erros_notas_canceladas", "Notas Canceladas c/ Valor"),
        ("erros_aliquota_invalida","Aliquotas Invalidas"),
        ("erros_d100",             "CT-e sem D190"),
        ("erros_nfe_duplicada",    "NF-e Duplicadas"),
        ("erros_cst",              "CST 00 sem ICMS"),
        ("erros_sequencia_nf",     "Saltos na Numeracao NF-e"),
    ]
    tem_erros = any(dados.get(k) for k, _ in erros_pdf)
    if tem_erros:
        pdf.set_fill_color(r, g, b)
        pdf.set_text_color(255, 255, 255)
        pdf.set_font("Arial", "B", 11)
        pdf.cell(0, 8, "  ERROS IDENTIFICADOS E BASE LEGAL", ln=True, fill=True)
        pdf.set_text_color(0, 0, 0)
        for chave, titulo in erros_pdf:
            lista = dados.get(chave, [])
            if not lista:
                continue
            pdf.set_font("Arial", "B", 10)
            pdf.set_text_color(200, 0, 0)
            pdf.cell(0, 6, _safe_pdf(f"  [{len(lista)}] {titulo}"), ln=True)
            bl = BASE_LEGAL.get(chave, {})
            if bl.get("norma"):
                pdf.set_font("Arial", "I", 8)
                pdf.set_text_color(80, 80, 80)
                pdf.multi_cell(0, 5, _safe_pdf(f"  Base legal: {bl['norma']}"))
            pdf.set_text_color(0, 0, 0)
        pdf.ln(2)

    # ── Rodapé ────────────────────────────────────────────────────────────────
    pdf.set_y(-20)
    pdf.set_fill_color(r, g, b)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Arial", "I", 8)
    pdf.cell(0, 8, _safe_pdf("Auditax 360 Enterprise — Documento gerado eletronicamente. Nao substitui analise profissional."),
             ln=True, align="C", fill=True)

    with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as tmp:
        pdf.output(tmp.name)
        with open(tmp.name, "rb") as f:
            b = f.read()
    os.remove(tmp.name)
    return b

# ══════════════════════════════════════════════════════════════════════════════
# MOTOR DE CRUZAMENTO ERP × SPED
# Absorvido do ValidadorFiscalPro — adaptado para rodar dentro do Auditax
# ══════════════════════════════════════════════════════════════════════════════

# Tolerâncias por tipo de imposto (sobrescrevíveis via env)
TOL_VALOR   = float(os.environ.get("TOL_VALOR",   "0.10"))
TOL_ICMS    = float(os.environ.get("TOL_ICMS",    "0.05"))
TOL_PIS     = float(os.environ.get("TOL_PIS",     "0.02"))
TOL_COFINS  = float(os.environ.get("TOL_COFINS",  "0.02"))
TOL_IPI     = float(os.environ.get("TOL_IPI",     "0.02"))

# Mapeamento flexível de colunas do ERP → nomes internos
# Usuário pode ter qualquer cabeçalho; tentamos várias variações
ALIASES_ERP = {
    "NUMERO_NOTA":     ["numero nf","número nf","nr nota","num_doc","numero_nota","numero nota","nro. documento","nf","nota"],
    "CNPJ_FORNECEDOR": ["cnpj emitente","cnpj fornecedor","cnpj","cpf/cnpj","cpf cnpj","fornecedor cnpj"],
    "VALOR_TOTAL":     ["valor total nf","valor total","vl. total","valor nota","valor_total","vltotal","valor nf"],
    "VALOR_ICMS":      ["valor icms","icms","vl. icms","vl icms","vlicms"],
    "VALOR_PIS":       ["valor pis","pis","vl. pis","vlpis"],
    "VALOR_COFINS":    ["valor cofins","cofins","vl. cofins","vlcofins"],
    "VALOR_IPI":       ["valor ipi","ipi","vl. ipi","vlipi"],
    "TIPO_OPERACAO":   ["tipo","entrada/saída","entrada saida","e/s","tipo operacao","tipo_operacao","fluxo"],
    "DATA_EMISSAO":    ["data emissão","data emissao","dt. emissão","dt emissao","data_emissao"],
    "SERIE":           ["série","serie","nr. série","nr serie","serie nota"],
    "CFOP":            ["cfop","cód. cfop","codigo cfop","cod cfop"],
}

def _normalizar_colunas_erp(df: pd.DataFrame) -> pd.DataFrame:
    """
    Tenta mapear cabeçalhos do ERP para nomes internos usando aliases.
    Colunas sem match são mantidas com nome original (não quebra o fluxo).
    """
    df = df.copy()
    df.columns = df.columns.str.strip()
    rename_map = {}
    cols_lower = {c.lower(): c for c in df.columns}
    for interno, aliases in ALIASES_ERP.items():
        if interno in df.columns:
            continue  # já tem o nome certo
        for alias in aliases:
            if alias.lower() in cols_lower:
                rename_map[cols_lower[alias.lower()]] = interno
                break
    df = df.rename(columns=rename_map)
    faltantes = [c for c in ["NUMERO_NOTA","CNPJ_FORNECEDOR","VALOR_TOTAL"] if c not in df.columns]
    if faltantes:
        log.warning(f"[ERP] Colunas obrigatórias não encontradas: {faltantes}. Verifique o cabeçalho do Excel.")
    return df

def _higienizar_erp(df: pd.DataFrame) -> pd.DataFrame:
    """Limpa CNPJ, número de nota e valores monetários."""
    df = df.copy()
    if "CNPJ_FORNECEDOR" in df.columns:
        df["CNPJ_FORNECEDOR"] = (df["CNPJ_FORNECEDOR"].astype(str)
            .str.replace(r"[.\-/\s]", "", regex=True).str.strip().str.zfill(14))
    if "NUMERO_NOTA" in df.columns:
        df["NUMERO_NOTA"] = (df["NUMERO_NOTA"].astype(str)
            .str.replace(r"\D", "", regex=True).str.strip())
    for col in ["VALOR_TOTAL","VALOR_ICMS","VALOR_PIS","VALOR_COFINS","VALOR_IPI"]:
        if col in df.columns:
            df[col] = (df[col].astype(str)
                .str.replace(r"[R$\s]", "", regex=True)
                .str.replace(r"\.(?=\d{3})", "", regex=True)
                .str.replace(",", ".", regex=False)
                .pipe(pd.to_numeric, errors="coerce").fillna(0.0))
    if "TIPO_OPERACAO" in df.columns:
        df["TIPO_OPERACAO"] = (df["TIPO_OPERACAO"].astype(str).str.upper().str.strip()
            .replace({"E":"ENTRADA","S":"SAIDA","SAÍDA":"SAIDA","0":"ENTRADA","1":"SAIDA"}))
    else:
        df["TIPO_OPERACAO"] = "INDETERMINADO"
    df["CHAVE_COMPOSTA"] = (df.get("NUMERO_NOTA", pd.Series([""] * len(df)))
        .astype(str) + "|" + df.get("CNPJ_FORNECEDOR", pd.Series([""] * len(df))).astype(str))
    return df

def _verificar_divergencias(df_ambos: pd.DataFrame,
                            tol_valor: float = TOL_VALOR,
                            tol_icms:  float = TOL_ICMS,
                            tol_pis:   float = TOL_PIS,
                            tol_cofins:float = TOL_COFINS,
                            tol_ipi:   float = TOL_IPI) -> list[dict]:
    """Detecta divergências de valor entre ERP e SPED nos registros em comum."""
    divergencias = []
    verificacoes = [
        ("VALOR_TOTAL",  tol_valor,  "VALOR_TOTAL_ERP",  "VALOR_TOTAL_SPED"),
        ("VALOR_ICMS",   tol_icms,   "VALOR_ICMS_ERP",   "VALOR_ICMS_SPED"),
        ("VALOR_PIS",    tol_pis,    "VALOR_PIS_ERP",    "VALOR_PIS_SPED"),
        ("VALOR_COFINS", tol_cofins, "VALOR_COFINS_ERP", "VALOR_COFINS_SPED"),
        ("VALOR_IPI",    tol_ipi,    "VALOR_IPI_ERP",    "VALOR_IPI_SPED"),
    ]
    for _, row in df_ambos.iterrows():
        campos_div = []
        for campo, tol, col_e, col_s in verificacoes:
            ve = float(row.get(col_e, 0) or 0)
            vs = float(row.get(col_s, 0) or 0)
            if abs(ve - vs) > tol:
                campos_div.append(campo)
        if campos_div:
            divergencias.append({
                "Chave Composta":  row.get("CHAVE_COMPOSTA",""),
                "Nota":            row.get("NUMERO_NOTA_ERP", row.get("NUMERO_NOTA_SPED","")),
                "CNPJ Emitente":   row.get("CNPJ_FORNECEDOR",""),
                "Chave NF-e":      row.get("CHAVE_NFE",""),
                "Tipo Operação":   row.get("TIPO_OPERACAO",""),
                "Campos Diverg.":  ", ".join(campos_div),
                "Valor ERP":       float(row.get("VALOR_TOTAL_ERP",0) or 0),
                "Valor SPED":      float(row.get("VALOR_TOTAL_SPED",0) or 0),
                "Diferença":       abs(float(row.get("VALOR_TOTAL_ERP",0) or 0) -
                                       float(row.get("VALOR_TOTAL_SPED",0) or 0)),
                "ICMS ERP":        float(row.get("VALOR_ICMS_ERP",0) or 0),
                "ICMS SPED":       float(row.get("VALOR_ICMS_SPED",0) or 0),
                "Data Emissão":    row.get("DATA_EMISSAO",""),
            })
    return divergencias

def cruzar_erp_sped(df_erp_raw: pd.DataFrame, dados_sped: dict,
                    tol_valor: float = TOL_VALOR, tol_icms: float = TOL_ICMS,
                    tol_pis: float = TOL_PIS, tol_cofins: float = TOL_COFINS,
                    tol_ipi: float = TOL_IPI) -> dict:
    """
    Motor principal de cruzamento ERP × SPED.
    Recebe o DataFrame bruto do ERP e o dict de dados já processado pelo engine SPED.
    Retorna dict com 6 relatórios (falta SPED entrada/saída, falta ERP entrada/saída,
    divergência valor entrada/saída) + métricas resumo.
    """
    # Prepara SPED como DataFrame
    c100_lista = list(dados_sped.get("c100_por_chave", {}).values())
    if not c100_lista:
        return {"erro": "Nenhum registro C100 válido encontrado no SPED processado."}

    df_sped = pd.DataFrame(c100_lista)

    # Prepara ERP
    df_erp = _normalizar_colunas_erp(df_erp_raw)
    df_erp = _higienizar_erp(df_erp)

    if "CHAVE_COMPOSTA" not in df_erp.columns or "CHAVE_COMPOSTA" not in df_sped.columns:
        return {"erro": "Não foi possível gerar chave composta. Verifique colunas do ERP."}

    resultado = {
        "total_erp": len(df_erp),
        "total_sped": len(df_sped),
        "entrada_falta_sped": [],
        "entrada_falta_erp": [],
        "entrada_divergencias": [],
        "saida_falta_sped": [],
        "saida_falta_erp": [],
        "saida_divergencias": [],
        "erro": None,
    }

    for tipo in ("ENTRADA", "SAIDA"):
        # CORREÇÃO: df.get() em pandas retorna a coluna (Series), não funciona com ==
        # Usar df[col] com verificação de existência
        df_e = (df_erp[df_erp["TIPO_OPERACAO"] == tipo].copy()
                if "TIPO_OPERACAO" in df_erp.columns else df_erp.copy())
        df_s = (df_sped[df_sped["TIPO_OPERACAO"] == tipo].copy()
                if "TIPO_OPERACAO" in df_sped.columns else df_sped.copy())

        if df_e.empty and df_s.empty:
            continue

        merged = pd.merge(
            df_e, df_s,
            on="CHAVE_COMPOSTA", how="outer",
            suffixes=("_ERP","_SPED"), indicator=True
        )

        chave = tipo.lower()
        # Falta no SPED: está no ERP mas não no SPED
        falta_sped = merged[merged["_merge"] == "left_only"].copy()
        resultado[f"{chave}_falta_sped"] = falta_sped[[
            c for c in ["CHAVE_COMPOSTA","NUMERO_NOTA","CNPJ_FORNECEDOR",
                        "VALOR_TOTAL","VALOR_ICMS","DATA_EMISSAO","CFOP"] if c in falta_sped.columns
        ]].to_dict("records")

        # Falta no ERP: está no SPED mas não no ERP
        falta_erp = merged[merged["_merge"] == "right_only"].copy()
        resultado[f"{chave}_falta_erp"] = falta_erp[[
            c for c in ["CHAVE_COMPOSTA","NUMERO_NOTA_SPED","CNPJ_FORNECEDOR",
                        "VALOR_TOTAL_SPED","VALOR_ICMS_SPED","DATA_EMISSAO","CHAVE_NFE"] if c in falta_erp.columns
        ]].rename(columns={"NUMERO_NOTA_SPED":"NUMERO_NOTA","VALOR_TOTAL_SPED":"VALOR_TOTAL",
                            "VALOR_ICMS_SPED":"VALOR_ICMS"}).to_dict("records")

        # Divergências de valor: em ambos mas com diferença acima da tolerância
        ambos = merged[merged["_merge"] == "both"].copy()
        resultado[f"{chave}_divergencias"] = _verificar_divergencias(
            ambos, tol_valor=tol_valor, tol_icms=tol_icms,
            tol_pis=tol_pis, tol_cofins=tol_cofins, tol_ipi=tol_ipi
        )

    total_div = sum(len(resultado[k]) for k in resultado if k.endswith(("_falta_sped","_falta_erp","_divergencias")))
    resultado["total_divergencias"] = total_div
    log.info(f"[CRUZAMENTO ERP] Total divergências: {total_div} (ERP:{resultado['total_erp']} × SPED:{resultado['total_sped']})")
    return resultado

# ══════════════════════════════════════════════════════════════════════════════
# UI — STREAMLIT
# ══════════════════════════════════════════════════════════════════════════════

st.set_page_config(page_title="Auditax 360º", layout="wide", page_icon="🏢")
st.markdown("""
<style>
  .plan-tag{padding:3px 10px;border-radius:20px;font-weight:700;font-size:.75rem;color:#fff}
  .p-trial{background:#6B7280} .p-starter{background:#3B82F6}
  .p-profissional{background:#8B5CF6} .p-enterprise{background:#059669}
  .info-box{background:#eff6ff;border:1px solid #93c5fd;padding:14px;border-radius:8px;margin-bottom:18px}
  .warn-box{background:#fffbeb;border:1px solid #fcd34d;padding:12px;border-radius:8px;margin-bottom:14px}
  [data-testid="stSidebar"]{background:#f9fafb}
</style>""", unsafe_allow_html=True)

# ── tela de login ──────────────────────────────────────────────────────────────
if "user" not in st.session_state:
    st.session_state["user"] = None
    st.session_state["tenant"] = None

if not st.session_state["user"]:
    col = st.columns([1, 1.4, 1])[1]
    with col:
        st.markdown("## 🔐 Auditax 360º")
        tab_login, tab_reg = st.tabs(["Entrar", "Criar conta"])

        with tab_login:
            email = st.text_input("E-mail")
            senha = st.text_input("Senha", type="password")
            if st.button("Entrar", use_container_width=True):
                u, t, err = autenticar(email, senha)
                if u:
                    st.session_state["user"]   = u
                    st.session_state["tenant"] = t
                    st.rerun()
                else:
                    st.error(err or "E-mail ou senha incorretos.")
            st.caption("💡 Demo: admin@auditax.com | Senha: admin123")

        with tab_reg:
            st.info("Crie uma conta com 14 dias de trial gratuito.")
            nome_emp = st.text_input("Nome da empresa")
            cnpj_emp = st.text_input("CNPJ (opcional)")
            nome_adm = st.text_input("Seu nome")
            email_adm = st.text_input("Seu e-mail", key="reg_email")
            senha_adm = st.text_input("Senha (mín. 8 caracteres)", type="password", key="reg_senha")
            if st.button("Criar conta grátis", use_container_width=True):
                if not nome_emp or not nome_adm or not email_adm or len(senha_adm) < 8:
                    st.error("Preencha todos os campos. Senha mínima de 8 caracteres.")
                else:
                    tid = criar_tenant(nome_emp, cnpj_emp, trial=True)
                    uid, _ = criar_usuario(tid, email_adm, nome_adm, "admin", senha_adm)
                    u, t, err = autenticar(email_adm, senha_adm)
                    if u:
                        st.session_state["user"]   = u
                        st.session_state["tenant"] = t
                        st.rerun()
                    elif err:
                        st.error(err)
    st.stop()

# ── estado da sessão ───────────────────────────────────────────────────────────
USER   = st.session_state["user"]
TENANT = st.session_state["tenant"]
PLANO_INFO = get_plano(TENANT)
PAPEL  = USER.get("papel", "viewer")
TENANT_ID = TENANT["id"]
USER_ID   = USER["id"]

# ── sidebar ────────────────────────────────────────────────────────────────────
with st.sidebar:
    pnome = PLANO_INFO["nome"].lower()
    st.markdown(f"### 👋 {USER['nome']}")
    st.markdown(f"<span class='plan-tag p-{pnome}'>{PLANO_INFO['label']}</span>", unsafe_allow_html=True)

    if PLANO_INFO.get("trial_restante") is not None:
        dias = PLANO_INFO["trial_restante"]
        st.warning(f"Trial: {dias} dias restantes")

    pode, msg_quota = verificar_quota(TENANT_ID, PLANO_INFO)
    st.caption(msg_quota)

    # Badge alertas não lidos
    alertas_nao_lidos = buscar_alertas(TENANT_ID, apenas_nao_lidos=True)
    if alertas_nao_lidos:
        st.warning(f"🔔 {len(alertas_nao_lidos)} alerta(s) não lido(s)")

    MENUS_BASE = ["🏠 Dashboard", "🛠️ Correções (PVA)",
                  "⚖️ Auditoria & Cadastros", "🔌 Cruzamento XML",
                  "📊 Reforma Tributária", "📈 Histórico & Score",
                  "🔀 Cruzamento ERP × SPED", "💡 EFD-Contribuições", "🏢 Comparativo Grupo", "🔔 Alertas"]
    MENUS_ADMIN = MENUS_BASE + ["👥 Usuários & Empresa", "⚙️ Conta & Plano",
                                  "📋 Log de Acesso", "🔧 Regras Personalizadas"]
    menus = MENUS_ADMIN if PAPEL == "admin" else MENUS_BASE
    menu = st.radio("Menu:", menus)

    if PAPEL in ("admin", "auditor"):
        st.divider()
        uploaded = st.file_uploader("📁 Arquivo SPED (.txt)", type="txt")
    else:
        uploaded = None

    st.divider()
    if st.button("Sair", use_container_width=True):
        st.session_state["user"]   = None
        st.session_state["tenant"] = None
        st.rerun()

# ══════════════════════════════════════════════════════════════════════════════
# BLOQUEADOR 3 — lógica de upload assíncrono (corrigido)
# ══════════════════════════════════════════════════════════════════════════════
# CORREÇÃO: resultado do job é guardado em session_state (não em dict de módulo)
# para sobreviver a reruns. st.rerun() é chamado após capturar o resultado.

dados = None

if uploaded and tem_permissao(PAPEL, "auditar"):
    f_hash = hashlib.md5(uploaded.getvalue()).hexdigest()

    # ── Detecta estado atual ──────────────────────────────────────
    _hash_novo = st.session_state.get("file_hash") != f_hash
    _sem_dados = not st.session_state.get("dados_cache")
    _sem_job   = not st.session_state.get("job_id")
    # Flag: botão Processar foi clicado (file_hash zerado manualmente)
    _reprocess = (st.session_state.get("file_hash") is None) and _sem_dados and _sem_job

    # Mostra botão quando arquivo já foi visto mas não há dados nem job ativo
    if not _hash_novo and _sem_dados and _sem_job and not _reprocess:
        if st.sidebar.button("▶️ Processar SPED", type="primary", use_container_width=True):
            st.session_state["file_hash"] = None
            st.session_state["dados_cache"] = None
            st.rerun()

    # Arquivo novo OU botão Processar clicado → dispara processamento
    if _hash_novo or _reprocess:
        pode_proc, msg_q = verificar_quota(TENANT_ID, PLANO_INFO)
        if not pode_proc:
            st.error(f"🚫 {msg_q}")
            st.stop()
        conteudo = uploaded.getvalue().decode("latin-1", errors="replace")
        # Validação básica: arquivo deve começar com registro 0000 do SPED
        primeira_linha = conteudo.lstrip().split("\n")[0] if conteudo.strip() else ""
        if not primeira_linha.startswith("|0000|"):
            st.error("❌ Arquivo inválido: não é um SPED EFD. O arquivo deve iniciar com o registro |0000|.")
            st.stop()
        st.session_state["file_hash"]        = f_hash
        st.session_state["linhas"]           = conteudo.splitlines(keepends=True)
        st.session_state["sped_conteudo_raw"] = conteudo  # para regras personalizadas
        st.session_state["log"]              = []
        st.session_state["backups"]          = []
        st.session_state["aud_salva"]        = False
        st.session_state["dados_cache"]      = None
        st.session_state["job_erro"]         = None

        registrar_log(TENANT_ID, USER_ID, USER["email"], "upload_sped",
                      f"Arquivo: {uploaded.name} ({uploaded.size} bytes)")
        job_id = iniciar_processamento(conteudo)
        st.session_state["job_id"] = job_id
        # Força rerun imediato para entrar no loop de polling
        st.rerun()

    # Loop de polling: verifica o job a cada rerun
    job_id = st.session_state.get("job_id")
    if job_id:
        job = status_job(job_id)

        if job["status"] == "processando":
            prog = job["progresso"]
            st.info(f"⏳ Processando SPED... {prog}%")
            bar = st.progress(prog / 100)
            time.sleep(0.8)
            st.rerun()

        elif job["status"] == "erro":
            st.session_state["job_id"]   = None
            st.session_state["job_erro"] = job["erro"]
            _jr2, _jl2 = _get_job_store()
            with _jl2:
                _jr2.pop(job_id, None)
            st.rerun()

        elif job["status"] == "concluido" and job["dados"] is not None:
            st.session_state["dados_cache"] = job["dados"]
            _jid_concluido = job_id              # guarda ANTES de zerar
            st.session_state["job_id"] = None
            _jr2, _jl2 = _get_job_store()
            with _jl2:
                _jr2.pop(_jid_concluido, None)
            st.rerun()

        elif job["status"] == "não_encontrado":
            # Job sumiu (raro, mas pode ocorrer em reinício do servidor).
            # Re-dispara o processamento em vez de ficar silenciosamente parado.
            st.warning("⚠️ Processamento perdido. Reiniciando...")
            conteudo_retry = "".join(st.session_state.get("linhas", []))
            if conteudo_retry:
                novo_job_id = iniciar_processamento(conteudo_retry)
                st.session_state["job_id"] = novo_job_id
                st.rerun()
            else:
                st.session_state["job_id"] = None
                st.error("Não foi possível reiniciar o processamento. Faça upload novamente.")

    # Exibe erro de processamento se houver
    if st.session_state.get("job_erro"):
        st.error(f"❌ Erro no processamento: {st.session_state['job_erro']}")

    dados  = st.session_state.get("dados_cache")
    linhas = st.session_state.get("linhas", [])

    # Salva no banco uma única vez por arquivo
    if dados and not st.session_state.get("aud_salva", False):
        aud_id = salvar_auditoria(TENANT_ID, USER_ID, dados)
        if aud_id:
            st.session_state["aud_salva"] = True

# ══════════════════════════════════════════════════════════════════════════════
# TELAS
# ══════════════════════════════════════════════════════════════════════════════

if dados is None and menu not in ("👥 Usuários & Empresa", "⚙️ Conta & Plano"):
    if menu == "📈 Histórico & Score":
        st.header("📈 Histórico & Score")
        empresas = listar_empresas_tenant(TENANT_ID)
        if not empresas:
            st.info("Nenhuma empresa processada ainda neste tenant.")
        else:
            emp_sel = st.selectbox("Empresa:", [f"{e['nome']} — {e['cnpj']}" for e in empresas])
            cnpj_sel = empresas[[f"{e['nome']} — {e['cnpj']}" for e in empresas].index(emp_sel)]["cnpj"]
            hist = buscar_historico(TENANT_ID, cnpj_sel)
            if hist:
                df = pd.DataFrame(hist)
                st.dataframe(df, use_container_width=True)
            else:
                st.info("Sem histórico para esta empresa.")
    else:
        st.info("👈 Faça upload do arquivo SPED no menu lateral.")
    # continua para telas que não precisam de dados

# ── Dashboard ─────────────────────────────────────────────────────────────────
if not dados and menu == "🏠 Dashboard":
    st.header("📊 Dashboard de Auditoria")
    st.info("👋 Bem-vindo ao **Auditax 360° Enterprise**! Para começar, carregue um arquivo SPED no painel lateral.")
    st.markdown("---")
    st.subheader("🚀 Como usar em 3 passos")
    col1, col2, col3 = st.columns(3)
    with col1:
        st.markdown("### 1️⃣ Carregar SPED")
        st.markdown("Faça upload do arquivo `.txt` do SPED EFD-ICMS/IPI no painel lateral esquerdo.")
    with col2:
        st.markdown("### 2️⃣ Processar")
        st.markdown("Clique em **▶️ Processar SPED** e aguarde. O sistema analisa automaticamente todas as obrigações fiscais.")
    with col3:
        st.markdown("### 3️⃣ Analisar")
        st.markdown("Explore o Dashboard, Correções, Histórico e relatórios PDF com os resultados da auditoria.")
    st.markdown("---")
    st.subheader("🔍 O que o Auditax verifica")
    analises = [
        ("📋 Registro 0000", "Identificação da empresa e período"),
        ("📦 Bloco C", "Notas Fiscais de entrada e saída"),
        ("🚛 Bloco D", "Conhecimentos de Transporte (CT-e)"),
        ("💰 Bloco E", "Apuração de ICMS e ICMS-ST"),
        ("🏭 Bloco G", "CIAP — Controle de crédito do ativo permanente"),
        ("📊 Bloco H", "Inventário de estoque"),
        ("🔧 Bloco K", "Controle de produção e estoque"),
        ("⚖️ DIFAL", "Diferencial de alíquota entre estados"),
        ("📉 Créditos", "Aproveitamento indevido de créditos fiscais"),
        ("🔄 Cruzamento ERP", "Divergências entre ERP e SPED"),
        ("📈 Score Fiscal", "Índice de conformidade 0-100"),
        ("📄 Relatório PDF", "Relatório executivo para auditoria"),
    ]
    cols = st.columns(3)
    for i, (icon_title, desc) in enumerate(analises):
        with cols[i % 3]:
            st.markdown(f"**{icon_title}**  \n{desc}")
    st.stop()

if dados and menu == "🏠 Dashboard":
    st.header("📊 Dashboard de Auditoria")
    st.markdown(f"<div class='info-box'><b>🏢 {dados.get('nome_empresa')}</b> | "
                f"CNPJ: {dados.get('cnpj')} | Layout: {dados.get('versao_layout')} | "
                f"Período: {dados.get('dt_ini')} → {dados.get('dt_fin')}</div>",
                unsafe_allow_html=True)

    score, eg, eo = calcular_score(dados)
    c1, c2, c3, c4, c5 = st.columns(5)
    c1.metric("Score Fiscal", f"{score}/100")
    c2.metric("Linhas",  f"{dados['total_linhas']:,}")
    c3.metric("NF-e",    f"{len(dados['notas_sped']):,}")
    c4.metric("CT-e (Frete)", f"{dados.get('total_cte',0):,}",
              help="Conhecimentos de Transporte Eletrônico — Bloco D")
    c4_icms = dados.get("vl_icms_servicos_d190", 0.0)
    c5.metric("Erros Graves", eg, delta="atenção" if eg > 0 else None, delta_color="inverse")

    # Destaque CT-e quando há ICMS de frete
    if c4_icms > 0:
        saidas_nfe = dados.get("vl_icms_saidas_c190", 0.0)
        st.info(f"🚚 **Bloco D:** R$ {c4_icms:,.2f} de ICMS em {dados.get('total_cte',0)} CT-e "
                f"(frete) · NF-e: R$ {saidas_nfe:,.2f} · Total saídas: R$ {saidas_nfe+c4_icms:,.2f}")

    # ── Rating A–F por Bloco ───────────────────────────────────────────────────
    st.divider()
    st.subheader("🏅 Rating de Conformidade por Bloco")
    rating_blocos = calcular_rating_blocos(dados)
    cols_r = st.columns(len(rating_blocos))
    for i, (_, info) in enumerate(rating_blocos.items()):
        with cols_r[i]:
            st.markdown(f"**{info['bloco']}**")
            st.markdown(f"### {info['rating']}")
            st.caption(info["descricao"])
            if info["erros"] > 0:
                st.caption(f"⚠ {info['erros']} ocorrência(s)")
            else:
                st.caption("✅ Sem erros")
    st.divider()

    col1, col2 = st.columns(2)
    with col1:
        if HAS_FPDF:
            logo_bytes = st.session_state.get("logo_pdf_bytes")
            cor_pdf    = st.session_state.get("cor_pdf", "#1E3A5F")
            st.download_button("📄 Laudo PDF",
                               gerar_pdf(dados, logo_bytes=logo_bytes, cor_primaria=cor_pdf),
                               "Laudo.pdf", "application/pdf",
                               use_container_width=True)
    with col2:
        st.download_button("📊 Relatório Excel",
                           gerar_excel(dados, st.session_state.get("log")),
                           "Relatorio.xlsx",
                           "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                           use_container_width=True)

# ── Correções PVA ─────────────────────────────────────────────────────────────
elif dados and menu == "🛠️ Correções (PVA)":
    if not tem_permissao(PAPEL, "corrigir"):
        st.warning("Sem permissão para correções.")
        st.stop()
    st.header("🛠️ Saneamento de Erros")
    c1, c2, c3 = st.columns(3)
    with c1:
        if st.button("🔧 Reparar Quebras"):
            criar_backup(linhas, "Quebras")
            nl, lg = corrigir_quebras_linha(linhas)
            st.session_state["linhas"] = nl
            st.session_state["log"].extend(lg)
            st.rerun()
    with c2:
        if st.button("⬆️ Atualizar Layout 020"):
            criar_backup(linhas, "Layout")
            nl, lg = atualizar_versao(linhas)
            st.session_state["linhas"] = nl
            st.session_state["log"].extend(lg)
            st.rerun()
    with c3:
        if st.button("🔢 Recalcular Bloco 9"):
            criar_backup(linhas, "Bloco 9")
            nl, lg = recalcular_bloco9(linhas)
            st.session_state["linhas"] = nl
            st.session_state["log"].extend(lg)
            st.rerun()
    st.download_button("📥 Baixar SPED Validado",
                       "".join(st.session_state["linhas"]).encode("latin-1"),
                       "SPED_VALIDADO.txt")
    st.divider()
    st.subheader("🔄 Ponte Excel: Importar Correções (0200 e 0400)")
    planilha_up = st.file_uploader("Upload Excel (.xlsx)", type=["xlsx"])
    if planilha_up:
        try:
            xls = pd.ExcelFile(planilha_up)
            novos, msgs = [], []
            if "Falta_0400" in xls.sheet_names:
                df0400 = pd.read_excel(xls, sheet_name="Falta_0400")
                for _, row in df0400.iterrows():
                    cod  = str(row.get("Cód", row.iloc[0])).strip()
                    desc = str(row.get("Descrição", row.iloc[1])).strip()
                    novos.append(f"|0400|{cod}|{desc}|\r\n")
                msgs.append(f"{len(df0400)} naturezas (0400)")
            if "Falta_0200" in xls.sheet_names:
                df0200 = pd.read_excel(xls, sheet_name="Falta_0200")
                for _, row in df0200.iterrows():
                    cod  = str(row.get("Cód", row.iloc[0])).strip()
                    desc = str(row.get("Descrição", f"PROD {cod}")).strip()
                    unid = str(row.get("Unidade", "UN")).strip()
                    tipo = str(row.get("Tipo (00 a 99)", "00")).strip().zfill(2)
                    ncm  = str(row.get("NCM (8 dig)", "00000000")).strip()
                    aliq = str(row.get("Alíquota ICMS", "")).strip()
                    novos.append(f"|0200|{cod}|{desc}|||{unid}|{tipo}|{ncm}||||{aliq}||\r\n")
                msgs.append(f"{len(df0200)} produtos (0200)")
            if novos:
                st.success(f"Pronto para injetar: {', '.join(msgs)}.")
                if st.button("✨ Injetar Cadastros no TXT"):
                    criar_backup(linhas, "Injeção Excel")
                    fl, ins = [], False
                    for l in linhas:
                        if not ins and l.startswith("|0990|"):
                            fl.extend(novos); ins = True
                        fl.append(l)
                    if not ins:
                        fl.extend(novos)
                    st.session_state["linhas"] = fl
                    st.session_state["log"].append(f"Injetados {len(novos)} cadastros.")
                    st.rerun()
            else:
                st.warning("Abas 'Falta_0400' ou 'Falta_0200' não encontradas.")
        except Exception as e:
            st.error(f"Erro ao processar Excel: {e}")

# ── Auditoria & Cadastros (expandida) ────────────────────────────────────────
elif dados and menu == "⚖️ Auditoria & Cadastros":
    st.header("⚖️ Auditoria Fiscal")
    t1, t2, t3, t4, t5, t6 = st.tabs([
        "Apuração Bloco E", "Auto-Fix 0400",
        "Produtos 0200", "Outros Erros",
        "Inventário (H)", "CIAP / ST / DIFAL"
    ])
    with t1:
        saidas_nfe = dados.get("vl_icms_saidas_c190", 0.0)
        saidas_cte = dados.get("vl_icms_servicos_d190", 0.0)
        saidas     = saidas_nfe + saidas_cte
        debitos    = dados.get("vl_tot_debitos_e110", 0.0)
        ajustes    = dados.get("vl_ajustes_e111", 0.0)
        debito_liq = dados.get("vl_debito_liquido_bloco_e", debitos - ajustes)
        div = abs(saidas - debito_liq)

        # ── Bloco C — NF-e ────────────────────────────────────────────────
        st.markdown("**📄 Bloco C — NF-e (Notas Fiscais):**")
        c1, c2, c3 = st.columns(3)
        c1.metric("ICMS Saídas C190 (NF-e)", f"R$ {saidas_nfe:,.2f}")
        c2.metric("NF-e processadas", len(dados.get("notas_sped", {})))
        c3.metric("NF-e duplicadas", len(dados.get("erros_nfe_duplicada", [])))

        # ── Bloco D — CT-e ────────────────────────────────────────────────
        st.markdown("**🚚 Bloco D — CT-e (Conhecimento de Transporte):**")
        d1, d2, d3 = st.columns(3)
        d1.metric("ICMS Saídas D190 (CT-e)", f"R$ {saidas_cte:,.2f}")
        d2.metric("CT-e processados", dados.get("total_cte", 0))
        d3.metric("CT-e s/ D190 (erros)", len(dados.get("erros_d100", [])))

        if saidas_cte > 0:
            st.info(f"🚚 O Bloco D contribui R$ {saidas_cte:,.2f} de ICMS via fretes emitidos pela empresa.")

        # ── Bloco E — Apuração ─────────────────────────────────────────────
        st.markdown("**📊 Bloco E — Apuração ICMS:**")
        e1, e2, e3, e4 = st.columns(4)
        e1.metric("Total Saídas (C190+D190)", f"R$ {saidas:,.2f}")
        e2.metric("Débitos E110", f"R$ {debitos:,.2f}")
        e3.metric("Ajustes E111", f"R$ {ajustes:,.2f}")
        e4.metric("Divergência Líquida", f"R$ {div:,.2f}",
                  delta="⚠ verificar" if div > 2 else "✅ ok",
                  delta_color="inverse" if div > 2 else "normal")

        if dados.get("e111_ajustes"):
            st.subheader("Ajustes E111")
            st.dataframe(pd.DataFrame(dados["e111_ajustes"]), use_container_width=True)
        if dados.get("e116_obrigacoes"):
            st.subheader(f"Obrigações E116 — R$ {dados['vl_total_e116']:,.2f}")
            st.dataframe(pd.DataFrame(dados["e116_obrigacoes"]), use_container_width=True)

        # CT-e com erro
        if dados.get("erros_d100"):
            st.error(f"🚚 {len(dados['erros_d100'])} CT-e de saída com ICMS mas sem registro D190")
            st.dataframe(pd.DataFrame(dados["erros_d100"]), use_container_width=True)

        # CT-e detalhado
        if dados.get("d190_icms"):
            with st.expander(f"📋 D190 — ICMS por CFOP/CST ({len(dados['d190_icms'])} registros)"):
                st.dataframe(pd.DataFrame(dados["d190_icms"]), use_container_width=True)

        st.divider()
        for chave, titulo in [
            ("erros_notas_canceladas","Notas Canceladas com Valor"),
            ("erros_cst","Itens Tributados sem ICMS"),
            ("erros_credito_indevido","Créditos Indevidos"),
            ("erros_nfe_duplicada","NF-e com Chave Duplicada"),
            ("erros_sequencia_nf","Saltos na Numeração de NF-e"),
        ]:
            if dados.get(chave):
                st.warning(f"{titulo} ({len(dados[chave])})")
                st.dataframe(pd.DataFrame(dados[chave]), use_container_width=True)
    with t2:
        nats = [n for n in dados.get("mapa_0400",{}) if n not in dados.get("reg_0400",set())]
        if nats:
            lista = [{"Cód": n, "CFOP": dados["mapa_0400"][n],
                      "Descrição": get_cfop_descricao(dados["mapa_0400"][n])} for n in nats]
            st.dataframe(pd.DataFrame(lista), use_container_width=True)
            if st.button("✨ Criar 0400 Automaticamente"):
                novos = [f"|0400|{n['Cód']}|{n['Descrição']}|\r\n" for n in lista]
                fl, ins = [], False
                for l in linhas:
                    if not ins and l.startswith("|0990|"):
                        fl.extend(novos); ins = True
                    fl.append(l)
                if not ins: fl.extend(novos)
                st.session_state["linhas"] = fl
                registrar_log(TENANT_ID, USER_ID, USER["email"], "autofix_0400", f"{len(novos)} registros")
                st.rerun()
        else:
            st.success("✅ Tudo ok com registros 0400.")
    with t3:
        prods = list(dados.get("prods_uso",set()) - dados.get("reg_0200",set()))
        if prods:
            st.error(f"Faltam {len(prods)} produtos no 0200.")
            st.dataframe(pd.DataFrame({"Códigos faltantes": prods}))
        else:
            st.success("✅ Tudo ok com registros 0200.")
    with t4:
        for chave, titulo in [("erros_unidade","Divergência de Unidade"), ("erros_bc_icms","BC Zerada com ICMS"), ("erros_aliquota_invalida","Alíquotas Fora do Padrão")]:
            if dados.get(chave):
                st.warning(titulo)
                st.dataframe(pd.DataFrame(dados[chave]), use_container_width=True)
        if not dados.get("erros_unidade") and not dados.get("erros_bc_icms"):
            st.success("✅ Nenhuma inconsistência.")
    with t5:
        if dados.get("h010_inventario"):
            df_inv = pd.DataFrame([{"Código": k, **v} for k,v in dados["h010_inventario"].items()])
            st.metric("Total Inventário", f"R$ {dados['vl_total_inventario']:,.2f}")
            st.dataframe(df_inv, use_container_width=True)
        else:
            st.info("Nenhum registro H010 neste SPED.")
    with t6:
        col1, col2 = st.columns(2)
        with col1:
            st.subheader("CIAP — Crédito Ativo Imobilizado")
            if dados.get("g110_ciap"):
                st.metric("Total CIAP", f"R$ {dados['vl_credito_ciap']:,.2f}")
                st.dataframe(pd.DataFrame(dados["g110_ciap"]), use_container_width=True)
            else:
                st.info("Sem registros G110.")
        with col2:
            st.subheader("ICMS-ST sem Preenchimento")
            if dados.get("erros_icms_st"):
                st.warning(f"{len(dados['erros_icms_st'])} itens com ST sem BC/Valor")
                st.dataframe(pd.DataFrame(dados["erros_icms_st"]), use_container_width=True)
            else:
                st.success("✅ ST sem inconsistências.")
        if dados.get("erros_difal"):
            st.divider()
            st.subheader("DIFAL — Alíquotas Interestaduais Suspeitas")
            st.dataframe(pd.DataFrame(dados["erros_difal"]), use_container_width=True)

# ── Cruzamento ERP × SPED ────────────────────────────────────────────────────
elif menu == "🔀 Cruzamento ERP × SPED":
    st.header("🔀 Cruzamento ERP × SPED")
    st.markdown(
        "Faça o upload da exportação do ERP para cruzar com o SPED já processado. "
        "O sistema identifica notas que estão num lado mas não no outro, e divergências de valor."
    )

    if not dados:
        st.warning("Carregue um arquivo SPED primeiro no menu lateral.")
    else:
        notas_sped = len(dados.get("c100_por_chave", {}))
        st.info(f"SPED carregado: **{dados.get('nome_empresa','')}** — {notas_sped} notas NF-e válidas disponíveis para cruzamento.")

        erp_file = st.file_uploader("📊 Upload da planilha ERP (.xlsx / .csv)", type=["xlsx","xls","csv"])

        with st.expander("⚙️ Tolerâncias de divergência (valores padrão)"):
            c1,c2,c3,c4,c5 = st.columns(5)
            tol_v = c1.number_input("Valor Total (R$)", value=TOL_VALOR, min_value=0.0, step=0.01, format="%.2f")
            tol_i = c2.number_input("ICMS (R$)",       value=TOL_ICMS,  min_value=0.0, step=0.01, format="%.2f")
            tol_p = c3.number_input("PIS (R$)",        value=TOL_PIS,   min_value=0.0, step=0.01, format="%.2f")
            tol_c = c4.number_input("COFINS (R$)",     value=TOL_COFINS,min_value=0.0, step=0.01, format="%.2f")
            tol_ip= c5.number_input("IPI (R$)",        value=TOL_IPI,   min_value=0.0, step=0.01, format="%.2f")

        tipo_fluxo_erp = st.radio("Filtrar fluxo:", ["Ambos","Somente Entradas","Somente Saídas"], horizontal=True)

        if erp_file and st.button("▶ Executar Cruzamento", type="primary"):
            try:
                if erp_file.name.endswith(".csv"):
                    for sep in [";", ",", "\t"]:
                        try:
                            df_erp_raw = pd.read_csv(erp_file, dtype=str, sep=sep)
                            if len(df_erp_raw.columns) > 1:
                                break
                        except Exception:
                            continue
                else:
                    sheet_idx = st.session_state.get("erp_sheet", 0)
                    df_erp_raw = pd.read_excel(erp_file, dtype=str, sheet_name=sheet_idx)

                with st.spinner("Cruzando ERP × SPED..."):
                    resultado_crz = cruzar_erp_sped(
                        df_erp_raw, dados,
                        tol_valor=tol_v, tol_icms=tol_i,
                        tol_pis=tol_p, tol_cofins=tol_c, tol_ipi=tol_ip
                    )

                if resultado_crz.get("erro"):
                    st.error(resultado_crz["erro"])
                else:
                    st.session_state["resultado_cruzamento_erp"] = resultado_crz
                    registrar_log(TENANT_ID, USER_ID, USER["email"],
                                  "cruzamento_erp", f"ERP:{resultado_crz['total_erp']} SPED:{resultado_crz['total_sped']}")
            except Exception as e:
                st.error(f"Erro ao processar ERP: {e}")
                log.error(f"cruzamento_erp: {e}")

        # Exibe resultado se disponível
        crz = st.session_state.get("resultado_cruzamento_erp")
        if crz and not crz.get("erro"):
            total_div = crz.get("total_divergencias", 0)
            c1,c2,c3,c4 = st.columns(4)
            c1.metric("Notas no ERP",  crz["total_erp"])
            c2.metric("Notas no SPED", crz["total_sped"])
            c3.metric("Total Divergências", total_div,
                      delta="Risco" if total_div > 0 else None, delta_color="inverse")
            c4.metric("Cobertura ERP",
                      f"{crz['total_sped']/max(crz['total_erp'],1)*100:.0f}%" if crz["total_erp"] else "—")

            st.divider()

            SECOES = [
                ("🔴 Entrada — Falta no SPED",    "entrada_falta_sped",
                 "Nota no ERP sem correspondência no SPED. Risco de operação não declarada."),
                ("🔴 Entrada — Falta no ERP",     "entrada_falta_erp",
                 "Nota no SPED mas ausente no ERP. Possível crédito perdido ou lançamento esquecido."),
                ("🟡 Entrada — Divergência Valor","entrada_divergencias",
                 "Nota em ambos, mas valores diferem além da tolerância configurada."),
                ("🔴 Saída — Falta no SPED",      "saida_falta_sped",
                 "Venda lançada no ERP mas não declarada no SPED."),
                ("🔴 Saída — Falta no ERP",       "saida_falta_erp",
                 "Nota de saída no SPED mas não registrada no ERP."),
                ("🟡 Saída — Divergência Valor",  "saida_divergencias",
                 "Saída em ambos, mas valores diferem."),
            ]

            # Filtro de fluxo
            filtro_map = {"Ambos": None, "Somente Entradas": "entrada", "Somente Saídas": "saida"}
            filtro_fluxo = filtro_map[tipo_fluxo_erp]

            for titulo, chave, descricao in SECOES:
                if filtro_fluxo and not chave.startswith(filtro_fluxo):
                    continue
                registros = crz.get(chave, [])
                if not registros:
                    continue
                with st.expander(f"{titulo} — {len(registros)} ocorrências", expanded=len(registros) > 0):
                    st.caption(descricao)
                    df_show = pd.DataFrame(registros)
                    st.dataframe(df_show, use_container_width=True, height=280)
                    csv = df_show.to_csv(index=False, sep=";", encoding="utf-8-sig").encode("utf-8-sig")
                    st.download_button(
                        f"⬇️ Exportar {chave}.csv", csv,
                        f"{chave}_{datetime.now().strftime('%Y%m%d')}.csv", "text/csv"
                    )

            if total_div == 0:
                st.success("🏆 Cruzamento sem divergências. ERP e SPED estão consistentes.")

            # Resumo em gráfico
            if total_div > 0:
                st.divider()
                st.subheader("Resumo Visual")
                labels = ["Falta SPED Ent.","Falta ERP Ent.","Diverg. Ent.",
                          "Falta SPED Saí.","Falta ERP Saí.","Diverg. Saí."]
                valores = [len(crz.get(k,[])) for k in
                           ["entrada_falta_sped","entrada_falta_erp","entrada_divergencias",
                            "saida_falta_sped","saida_falta_erp","saida_divergencias"]]
                cores = ["#EF4444","#F59E0B","#FBBF24","#DC2626","#D97706","#FCD34D"]
                df_graf = pd.DataFrame({"Tipo": labels, "Qtd": valores, "Cor": cores})
                df_graf = df_graf[df_graf["Qtd"] > 0]
                fig = px.bar(df_graf, x="Tipo", y="Qtd", color="Tipo",
                             color_discrete_sequence=cores[:len(df_graf)],
                             title="Distribuição das Divergências ERP × SPED")
                fig.update_layout(showlegend=False)
                st.plotly_chart(fig, use_container_width=True)

# ── EFD-Contribuições × SPED Fiscal ──────────────────────────────────────────
elif menu == "💡 EFD-Contribuições":
    st.header("💡 Cruzamento SPED Fiscal × EFD-Contribuições")
    st.markdown(
        "Carregue o arquivo EFD-Contribuições (PIS/COFINS) e o sistema identifica "
        "inconsistências entre o ICMS declarado no SPED Fiscal e as bases de PIS/COFINS."
    )

    if not dados:
        st.warning("Carregue um arquivo SPED Fiscal primeiro no menu lateral.")
    else:
        efd_c_file = st.file_uploader("📁 EFD-Contribuições (.txt)", type=["txt"], key="efd_contrib")

        if efd_c_file:
            conteudo_c = efd_c_file.getvalue().decode("latin-1", errors="replace")
            primeira = conteudo_c.lstrip().split("\n")[0]
            if not (primeira.startswith("|0000|") and "PIS" in conteudo_c[:2000].upper()):
                st.error("❌ Arquivo não parece ser um EFD-Contribuições válido.")
            else:
                with st.spinner("Processando EFD-Contribuições..."):
                    # Parser simplificado — extrai registros M200 (apuração PIS) e M600 (apuração COFINS)
                    linhas_efd = conteudo_c.splitlines()
                    m200, m600, c170_pis, c170_cof = [], [], [], []
                    empresa_efd, cnpj_efd, periodo_efd = "", "", ""
                    for ln in linhas_efd:
                        campos = ln.strip().split("|")
                        if len(campos) < 2:
                            continue
                        reg = campos[1].upper()
                        if reg == "0000" and len(campos) > 7:
                            periodo_efd = campos[2] if len(campos) > 2 else ""
                            cnpj_efd   = campos[8] if len(campos) > 8 else ""
                            empresa_efd= campos[9] if len(campos) > 9 else ""
                        elif reg == "M200" and len(campos) > 10:
                            # VL_TOT_CONT_NC_PER, VL_TOT_CRED_DESC_NC, VL_CONT_DIFER, VL_TOT_CONT_NC_REC
                            try:
                                vl_pis = float(campos[2].replace(",",".") or 0)
                                m200.append({"campo": "M200", "valor_pis": vl_pis, "linha": ln[:80]})
                            except Exception:
                                pass
                        elif reg == "M600" and len(campos) > 10:
                            try:
                                vl_cof = float(campos[2].replace(",",".") or 0)
                                m600.append({"campo": "M600", "valor_cofins": vl_cof, "linha": ln[:80]})
                            except Exception:
                                pass

                    total_pis    = sum(r["valor_pis"]    for r in m200)
                    total_cofins = sum(r["valor_cofins"]  for r in m600)

                st.success("✅ EFD-Contribuições processado!")

                # Dados do SPED Fiscal para comparação
                saidas_icms = dados.get("vl_icms_saidas_c190", 0.0) + dados.get("vl_icms_servicos_d190", 0.0)
                fat_estimado_fiscal = saidas_icms / 0.12 if saidas_icms > 0 else 0

                # PIS/COFINS esperado sobre o faturamento estimado (regime não cumulativo)
                pis_esperado    = fat_estimado_fiscal * 0.0165
                cofins_esperado = fat_estimado_fiscal * 0.076
                div_pis    = abs(total_pis - pis_esperado)
                div_cofins = abs(total_cofins - cofins_esperado)

                st.subheader("📊 Resultado do Cruzamento")
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown("**SPED Fiscal (EFD-ICMS/IPI)**")
                    st.metric("ICMS Saídas Declarado", f"R$ {saidas_icms:,.2f}")
                    st.metric("Faturamento Estimado (÷12%)", f"R$ {fat_estimado_fiscal:,.2f}")
                with col2:
                    st.markdown("**EFD-Contribuições (PIS/COFINS)**")
                    st.metric("PIS Apurado (M200)", f"R$ {total_pis:,.2f}")
                    st.metric("COFINS Apurado (M600)", f"R$ {total_cofins:,.2f}")

                st.divider()
                st.subheader("⚠️ Análise de Consistência")

                col_p, col_c = st.columns(2)
                with col_p:
                    st.markdown("**PIS**")
                    st.metric("PIS Esperado (1,65%)", f"R$ {pis_esperado:,.2f}")
                    st.metric("PIS Declarado", f"R$ {total_pis:,.2f}")
                    if div_pis > 100:
                        st.warning(f"⚠ Divergência PIS: R$ {div_pis:,.2f}")
                        st.caption(get_base_legal("erros_credito_indevido"))
                    else:
                        st.success("✅ PIS consistente")
                with col_c:
                    st.markdown("**COFINS**")
                    st.metric("COFINS Esperado (7,6%)", f"R$ {cofins_esperado:,.2f}")
                    st.metric("COFINS Declarado", f"R$ {total_cofins:,.2f}")
                    if div_cofins > 100:
                        st.warning(f"⚠ Divergência COFINS: R$ {div_cofins:,.2f}")
                        st.caption(get_base_legal("erros_credito_indevido"))
                    else:
                        st.success("✅ COFINS consistente")

                if m200 or m600:
                    with st.expander("📋 Registros M200 (PIS) extraídos"):
                        st.dataframe(pd.DataFrame(m200) if m200 else pd.DataFrame([{"info": "Nenhum M200 encontrado"}]),
                                     use_container_width=True)
                    with st.expander("📋 Registros M600 (COFINS) extraídos"):
                        st.dataframe(pd.DataFrame(m600) if m600 else pd.DataFrame([{"info": "Nenhum M600 encontrado"}]),
                                     use_container_width=True)

                st.caption("ℹ️ As alíquotas esperadas (1,65% PIS / 7,6% COFINS) são do regime não-cumulativo. "
                           "Para o cumulativo (0,65% / 3%), ajuste conforme o regime da empresa.")
                registrar_log(TENANT_ID, USER_ID, USER["email"], "cruzamento_efd_contribuicoes",
                              f"PIS:{total_pis:.2f} COFINS:{total_cofins:.2f}")

# ── Comparativo Grupo ─────────────────────────────────────────────────────────
elif menu == "🏢 Comparativo Grupo":
    st.header("🏢 Comparativo entre Empresas do Grupo")
    comp = buscar_comparativo_tenant(TENANT_ID)
    if not comp:
        st.info("Processe SPEDs de pelo menos uma empresa para ver o comparativo.")
    else:
        df_comp = pd.DataFrame(comp)
        cols = st.columns(min(len(comp), 4))
        for idx, row in enumerate(comp[:4]):
            cor = "🟢" if row["score"]>=75 else "🟡" if row["score"]>=60 else "🔴"
            cols[idx].metric(f"{cor} {row['nome'][:18]}", f"{row['score']}/100", f"{row['total_erros']} erros")
        st.divider()
        fig_comp = px.bar(df_comp, x="nome", y="score", color="score",
            color_continuous_scale=["#EF4444","#F59E0B","#22C55E"], range_color=[0,100],
            title="Score Fiscal por Empresa")
        fig_comp.add_hline(y=75, line_dash="dash", line_color="orange")
        fig_comp.update_layout(coloraxis_showscale=False, yaxis_range=[0,100])
        st.plotly_chart(fig_comp, use_container_width=True)
        if "divergencia_icms" in df_comp.columns:
            st.plotly_chart(px.bar(df_comp, x="nome", y="divergencia_icms",
                title="Divergência ICMS por Empresa (R$)", color_discrete_sequence=["#EF4444"]),
                use_container_width=True)
        colunas_show = [c for c in ["nome","cnpj","uf","periodo","score","total_erros",
                        "erros_graves","divergencia_icms"] if c in df_comp.columns]
        st.dataframe(df_comp[colunas_show], use_container_width=True)

# ── Alertas ───────────────────────────────────────────────────────────────────
elif menu == "🔔 Alertas":
    st.header("🔔 Alertas & Notificações")
    alertas = buscar_alertas(TENANT_ID, apenas_nao_lidos=False)
    nao_lidos = [a for a in alertas if not a["lido"]]
    col1, col2 = st.columns([3,1])
    with col1:
        st.metric("Alertas não lidos", len(nao_lidos))
    with col2:
        if nao_lidos and st.button("Marcar todos como lidos"):
            marcar_alertas_lidos(TENANT_ID)
            st.rerun()
    if not alertas:
        st.success("✅ Nenhum alerta até o momento.")
    else:
        ICONES = {"erro_grave":"🔴","score_critico":"🚨","queda_score":"📉","divergencia_icms":"⚠️"}
        for a in alertas:
            icone = ICONES.get(a["tipo"], "ℹ️")
            lido_str = "" if a["lido"] else " • **Não lido**"
            with st.expander(f"{icone} {a['mensagem']}{lido_str}", expanded=not a["lido"]):
                st.caption(f"Tipo: {a['tipo']} | {a.get('empresa_nome','')} | {a['criado_em'][:16]}")
    if not NOTIF_ENABLED:
        st.divider()
        st.info("📧 Configure SMTP_HOST, SMTP_USER e SMTP_PASS para ativar notificações por e-mail.")

# ── Simulador Reforma Tributária ─────────────────────────────────────────────
elif menu == "📊 Reforma Tributária":
    st.header("📊 Simulador de Impacto — Reforma Tributária (IBS/CBS)")
    st.caption("LC 214/2024 — Transição 2026–2032. Baseado nos dados do SPED carregado.")

    # Alíquotas de referência (Comitê Gestor / Receita Federal — estimativas divulgadas)
    # Fonte: PLP 68/2024 e notas técnicas do MF — alíquota-teto IBS+CBS ≈ 26,5% (estimativa 2024)
    ALIQ_IBS_CBS_REF = 0.265   # estimativa central do governo
    ALIQ_IBS_CBS_MIN = 0.230
    ALIQ_IBS_CBS_MAX = 0.280

    # Cronograma de transição (redutor CBS/IBS por ano — percentual do sistema novo)
    TRANSICAO = {
        2026: 0.01,   # 1% CBS teste
        2027: 0.01,   # ainda 1% CBS
        2028: 0.07,   # início CBS pleno + IBS 1/4 das alíquotas UF/Mun
        2029: 0.14,
        2030: 0.25,
        2031: 0.40,
        2032: 0.60,
        2033: 1.00,   # sistema novo pleno (IS separado)
    }

    with st.expander("ℹ️ Sobre a simulação", expanded=False):
        st.markdown("""
        Esta simulação estima o impacto financeiro da Reforma Tributária nos tributos sobre o consumo da empresa.
        - **IBS** substitui ICMS (estados) e ISS (municípios)
        - **CBS** substitui PIS e COFINS
        - **IS** (Imposto Seletivo) incide sobre produtos prejudiciais à saúde/ambiente
        - A alíquota total estimada é de **26,5%** (teto aprovado no PLP 68/2024)
        - A transição ocorre entre 2026 e 2032; o sistema novo é pleno a partir de 2033
        - **Esta é uma estimativa para planejamento. Consulte um especialista tributário.**
        """)

    if not dados:
        st.info("👈 Carregue um arquivo SPED para calcular o impacto com base nos dados reais da empresa.")
        # Simulação manual
        st.subheader("📐 Simulação Manual")
        col1, col2 = st.columns(2)
        with col1:
            fat_manual = st.number_input("Faturamento Bruto Anual (R$)", value=1_000_000.0,
                                          min_value=0.0, step=10_000.0, format="%.2f")
            aliq_icms_atual = st.number_input("Alíquota ICMS atual (%)", value=12.0, min_value=0.0, max_value=30.0) / 100
        with col2:
            aliq_pis_cofins = st.number_input("PIS+COFINS atual (%)", value=3.65, min_value=0.0, max_value=15.0) / 100
            aliq_nova = st.slider("Alíquota IBS+CBS estimada (%)", 23.0, 28.0, 26.5, 0.1) / 100
        carga_atual  = fat_manual * (aliq_icms_atual + aliq_pis_cofins)
        carga_nova   = fat_manual * aliq_nova
        delta        = carga_nova - carga_atual
        col_a, col_b, col_c = st.columns(3)
        col_a.metric("Carga Atual (ICMS+PIS/COFINS)", f"R$ {carga_atual:,.2f}")
        col_b.metric("Carga Nova (IBS+CBS)", f"R$ {carga_nova:,.2f}")
        col_c.metric("Variação", f"R$ {delta:+,.2f}", delta=f"{delta/carga_atual*100:+.1f}%" if carga_atual else "—",
                     delta_color="inverse" if delta > 0 else "normal")
    else:
        # Dados reais do SPED
        fat_sped = dados.get("vl_icms_saidas_c190", 0.0) + dados.get("vl_icms_servicos_d190", 0.0)
        # Estimativa de faturamento bruto via saídas (ICMS ÷ alíquota média)
        aliq_media_estimada = 0.12
        fat_estimado = fat_sped / aliq_media_estimada if fat_sped > 0 else 0

        st.subheader("📐 Dados extraídos do SPED")
        col1, col2, col3 = st.columns(3)
        col1.metric("ICMS Declarado (C190+D190)", f"R$ {fat_sped:,.2f}")
        col2.metric("Faturamento Estimado", f"R$ {fat_estimado:,.2f}",
                    help="Estimativa: ICMS ÷ alíquota média de 12%")
        col3.metric("Período", f"{dados.get('dt_ini','')} → {dados.get('dt_fin','')}")

        st.divider()
        st.subheader("⚙️ Parâmetros da simulação")
        col_p1, col_p2, col_p3 = st.columns(3)
        with col_p1:
            fat_base = st.number_input("Faturamento anual (R$)",
                                        value=round(fat_estimado * 12, 2) if fat_estimado else 1_000_000.0,
                                        min_value=0.0, step=10_000.0, format="%.2f")
        with col_p2:
            aliq_icms_atual = st.number_input("Alíquota ICMS atual (%)", value=12.0, min_value=0.0, max_value=30.0) / 100
            aliq_pis_cofins = st.number_input("PIS+COFINS atual (%)", value=3.65, min_value=0.0, max_value=15.0) / 100
        with col_p3:
            aliq_ibs_cbs = st.slider("Alíquota IBS+CBS (%)", 23.0, 28.0, 26.5, 0.1) / 100
            tem_is = st.checkbox("Produto com Imposto Seletivo (IS)?", value=False)
            aliq_is = st.number_input("Alíquota IS (%)", value=0.0, min_value=0.0, max_value=100.0,
                                       disabled=not tem_is) / 100 if tem_is else 0.0

        carga_atual = fat_base * (aliq_icms_atual + aliq_pis_cofins)
        carga_nova  = fat_base * (aliq_ibs_cbs + aliq_is)
        delta_total = carga_nova - carga_atual

        st.divider()
        st.subheader("📊 Resultado — Impacto Estimado")
        c1, c2, c3, c4 = st.columns(4)
        c1.metric("Carga Atual/ano", f"R$ {carga_atual:,.2f}")
        c2.metric("Carga Nova/ano (IBS+CBS)", f"R$ {carga_nova:,.2f}")
        c3.metric("Variação Absoluta", f"R$ {delta_total:+,.2f}",
                  delta=f"{delta_total/carga_atual*100:+.1f}%" if carga_atual else "—",
                  delta_color="inverse" if delta_total > 0 else "normal")
        c4.metric("Alíquota Efetiva Nova", f"{(aliq_ibs_cbs+aliq_is)*100:.1f}%")

        if delta_total > 0:
            st.warning(f"⚠️ **Aumento de carga estimado:** R$ {delta_total:,.2f}/ano. Avalie enquadramento no Simples Nacional ou regimes especiais.")
        elif delta_total < 0:
            st.success(f"✅ **Redução de carga estimada:** R$ {abs(delta_total):,.2f}/ano. A empresa pode se beneficiar do novo sistema.")
        else:
            st.info("O impacto estimado é neutro para esta alíquota configurada.")

        st.divider()
        st.subheader("📅 Projeção por Ano de Transição (2026–2033)")
        anos, cargas_ant, cargas_nov, cargas_tot = [], [], [], []
        for ano, pct_novo in TRANSICAO.items():
            pct_ant = 1 - pct_novo
            c_ant = fat_base * (aliq_icms_atual + aliq_pis_cofins) * pct_ant
            c_nov = fat_base * (aliq_ibs_cbs + aliq_is) * pct_novo
            anos.append(str(ano))
            cargas_ant.append(round(c_ant, 2))
            cargas_nov.append(round(c_nov, 2))
            cargas_tot.append(round(c_ant + c_nov, 2))

        df_proj = pd.DataFrame({
            "Ano": anos,
            "Sistema Atual (ICMS+PIS/COFINS)": cargas_ant,
            "Sistema Novo (IBS+CBS)": cargas_nov,
            "Carga Total Estimada": cargas_tot,
        })
        st.dataframe(df_proj, use_container_width=True, hide_index=True)

        fig_proj = px.bar(df_proj, x="Ano",
                          y=["Sistema Atual (ICMS+PIS/COFINS)", "Sistema Novo (IBS+CBS)"],
                          barmode="stack",
                          title="Transição de Carga Tributária por Ano",
                          color_discrete_sequence=["#3B82F6", "#F59E0B"])
        fig_proj.add_scatter(x=df_proj["Ano"], y=df_proj["Carga Total Estimada"],
                             mode="lines+markers", name="Total", line=dict(color="#EF4444", width=2))
        st.plotly_chart(fig_proj, use_container_width=True)

        st.download_button("⬇️ Exportar Projeção CSV",
                           df_proj.to_csv(index=False, sep=";", encoding="utf-8-sig").encode("utf-8-sig"),
                           f"reforma_tributaria_{dados.get('cnpj','')}.csv", "text/csv")

        st.caption("⚠️ Simulação baseada em estimativas do PLP 68/2024 e notas técnicas do MF. "
                   "Alíquotas definitivas serão definidas pelo Comitê Gestor do IBS. Consulte um especialista.")

# ── Regras Personalizadas (admin) ─────────────────────────────────────────────
elif menu == "🔧 Regras Personalizadas":
    if PAPEL != "admin":
        st.error("Acesso restrito a administradores.")
        st.stop()

    st.header("🔧 Regras de Validação Personalizadas")
    st.caption("Crie regras customizadas para validar campos do SPED sem necessidade de programação.")

    # ── Inicializar tabela de regras_custom ──────────────────────────────────
    def _init_regras_custom():
        with _get_db() as cx:
            cx.execute("""
                CREATE TABLE IF NOT EXISTS regras_custom (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    tenant_id TEXT NOT NULL,
                    nome TEXT NOT NULL,
                    descricao TEXT,
                    registro_sped TEXT NOT NULL,
                    campo_posicao INTEGER NOT NULL,
                    condicao TEXT NOT NULL,
                    valor_referencia TEXT NOT NULL,
                    severidade TEXT DEFAULT 'Alerta',
                    ativo INTEGER DEFAULT 1,
                    criado_em TEXT DEFAULT (datetime('now'))
                )
            """)
            cx.commit()

    def _listar_regras(tenant_id: str) -> list[dict]:
        with _get_db() as cx:
            rows = cx.execute(
                "SELECT * FROM regras_custom WHERE tenant_id=? ORDER BY id DESC", (tenant_id,)
            ).fetchall()
            cols = [d[0] for d in cx.description]
            return [dict(zip(cols, r)) for r in rows]

    def _salvar_regra(tenant_id: str, dados_regra: dict) -> None:
        with _get_db() as cx:
            cx.execute("""
                INSERT INTO regras_custom
                (tenant_id, nome, descricao, registro_sped, campo_posicao,
                 condicao, valor_referencia, severidade, ativo)
                VALUES (?,?,?,?,?,?,?,?,1)
            """, (tenant_id, dados_regra["nome"], dados_regra["descricao"],
                  dados_regra["registro_sped"], dados_regra["campo_posicao"],
                  dados_regra["condicao"], dados_regra["valor_referencia"],
                  dados_regra["severidade"]))
            cx.commit()

    def _toggle_regra(regra_id: int, ativo: int) -> None:
        with _get_db() as cx:
            cx.execute("UPDATE regras_custom SET ativo=? WHERE id=?", (ativo, regra_id))
            cx.commit()

    def _deletar_regra(regra_id: int) -> None:
        with _get_db() as cx:
            cx.execute("DELETE FROM regras_custom WHERE id=?", (regra_id,))
            cx.commit()

    def _aplicar_regras_custom(linhas_sped: list[str], regras: list[dict]) -> list[dict]:
        """Aplica regras customizadas sobre as linhas do SPED e retorna violações."""
        violations = []
        for linha in linhas_sped:
            partes = linha.strip().split("|")
            if len(partes) < 2:
                continue
            registro = partes[1]
            for regra in regras:
                if regra["ativo"] != 1:
                    continue
                if regra["registro_sped"] != registro:
                    continue
                pos = regra["campo_posicao"]
                if pos >= len(partes):
                    continue
                valor_campo = partes[pos].strip()
                vref = regra["valor_referencia"].strip()
                cond = regra["condicao"]
                violou = False
                try:
                    if cond == "igual a":
                        violou = valor_campo != vref
                    elif cond == "diferente de":
                        violou = valor_campo == vref
                    elif cond == "contém":
                        violou = vref not in valor_campo
                    elif cond == "não contém":
                        violou = vref in valor_campo
                    elif cond == "maior que":
                        violou = float(valor_campo.replace(",", ".") or 0) <= float(vref.replace(",", "."))
                    elif cond == "menor que":
                        violou = float(valor_campo.replace(",", ".") or 0) >= float(vref.replace(",", "."))
                    elif cond == "está vazio":
                        violou = valor_campo != ""
                    elif cond == "não está vazio":
                        violou = valor_campo == ""
                except Exception:
                    pass
                if violou:
                    violations.append({
                        "Regra": regra["nome"],
                        "Registro": registro,
                        "Posição": pos,
                        "Valor Encontrado": valor_campo,
                        "Condição": f"{cond} '{vref}'",
                        "Severidade": regra["severidade"],
                        "Descrição": regra.get("descricao", ""),
                    })
        return violations

    _init_regras_custom()

    tab_lista, tab_nova, tab_aplicar = st.tabs(["📋 Regras Ativas", "➕ Nova Regra", "▶️ Aplicar no SPED"])

    # ── Aba: lista de regras ─────────────────────────────────────────────────
    with tab_lista:
        regras = _listar_regras(TENANT_ID)
        if not regras:
            st.info("Nenhuma regra criada ainda. Use a aba **Nova Regra** para começar.")
        else:
            st.markdown(f"**{len(regras)} regra(s) cadastrada(s)**")
            for r in regras:
                ativo = r["ativo"] == 1
                col1, col2, col3 = st.columns([6, 1, 1])
                with col1:
                    sev_icon = {"Crítico": "🔴", "Alerta": "🟡", "Informativo": "🔵"}.get(r["severidade"], "⚪")
                    status_txt = "✅ Ativa" if ativo else "⏸️ Inativa"
                    st.markdown(
                        f"**{r['nome']}** {sev_icon} · `{r['registro_sped']}` campo `{r['campo_posicao']}` "
                        f"**{r['condicao']}** `{r['valor_referencia']}` · {status_txt}"
                    )
                    if r.get("descricao"):
                        st.caption(r["descricao"])
                with col2:
                    lbl = "⏸️ Pausar" if ativo else "▶️ Ativar"
                    if st.button(lbl, key=f"tog_{r['id']}"):
                        _toggle_regra(r["id"], 0 if ativo else 1)
                        st.rerun()
                with col3:
                    if st.button("🗑️ Excluir", key=f"del_{r['id']}"):
                        _deletar_regra(r["id"])
                        registrar_log(TENANT_ID, st.session_state.get("usuario_email","?"),
                                      "Excluiu regra customizada", r["nome"])
                        st.rerun()
                st.divider()

    # ── Aba: nova regra ──────────────────────────────────────────────────────
    with tab_nova:
        st.subheader("Criar Nova Regra de Validação")
        st.markdown("""
        **Como funciona:** Informe qual registro SPED você quer validar (ex: `C100`, `D100`),
        a posição do campo no pipe (`|REG|campo1|campo2|…` — posição 1 = REG, 2 = primeiro campo),
        a condição e o valor esperado. O sistema verificará cada linha do seu SPED.
        """)

        REGISTROS_COMUNS = [
            "C100", "C110", "C170", "C190", "C195",
            "D100", "D190", "D195",
            "E110", "E116", "E200", "E210",
            "0000", "0150", "0200", "0400",
            "G110", "H010",
        ]

        with st.form("form_nova_regra", clear_on_submit=True):
            nome_r = st.text_input("Nome da regra *", placeholder="Ex: ICMS zerado em operação tributada")
            desc_r = st.text_area("Descrição (opcional)", height=70,
                                  placeholder="Explique o objetivo desta regra para sua equipe.")
            col_a, col_b = st.columns(2)
            with col_a:
                reg_sped = st.selectbox("Registro SPED *", REGISTROS_COMUNS + ["Outro"])
                if reg_sped == "Outro":
                    reg_sped = st.text_input("Informe o registro:", max_chars=10).upper()
                campo_pos = st.number_input("Posição do campo *", min_value=2, max_value=50, value=4,
                                            help="Posição no pipe. 1=REG, 2=primeiro campo de dados, etc.")
            with col_b:
                CONDICOES = [
                    "igual a", "diferente de", "contém", "não contém",
                    "maior que", "menor que", "está vazio", "não está vazio",
                ]
                condicao = st.selectbox("Condição *", CONDICOES)
                valor_ref = st.text_input("Valor de referência *",
                                          placeholder="Ex: 0.00 ou CST inválido",
                                          disabled=condicao in ("está vazio", "não está vazio"))
                severidade = st.selectbox("Severidade", ["Crítico", "Alerta", "Informativo"])

            submitted = st.form_submit_button("💾 Salvar Regra", type="primary")
            if submitted:
                if not nome_r.strip() or not reg_sped.strip():
                    st.error("Nome e Registro SPED são obrigatórios.")
                else:
                    _salvar_regra(TENANT_ID, {
                        "nome": nome_r.strip(),
                        "descricao": desc_r.strip(),
                        "registro_sped": reg_sped.strip().upper(),
                        "campo_posicao": int(campo_pos),
                        "condicao": condicao,
                        "valor_referencia": valor_ref.strip() if condicao not in ("está vazio", "não está vazio") else "",
                        "severidade": severidade,
                    })
                    registrar_log(TENANT_ID, st.session_state.get("usuario_email","?"),
                                  "Criou regra customizada", nome_r)
                    st.success(f"✅ Regra **{nome_r}** salva com sucesso!")
                    st.rerun()

    # ── Aba: aplicar no SPED carregado ───────────────────────────────────────
    with tab_aplicar:
        st.subheader("▶️ Aplicar Regras no SPED Carregado")
        regras_ativas = [r for r in _listar_regras(TENANT_ID) if r["ativo"] == 1]
        if not regras_ativas:
            st.warning("Nenhuma regra ativa. Crie e ative regras na aba **Nova Regra**.")
        elif "sped_conteudo_raw" not in st.session_state:
            st.info("Faça o upload de um arquivo SPED na tela **📂 Upload SPED** primeiro para aplicar as regras.")
        else:
            linhas = st.session_state["sped_conteudo_raw"].splitlines()
            st.markdown(f"SPED carregado: **{len(linhas):,} linhas** · Regras ativas: **{len(regras_ativas)}**")
            if st.button("▶️ Executar Validação Personalizada", type="primary"):
                with st.spinner("Aplicando regras..."):
                    violacoes = _aplicar_regras_custom(linhas, regras_ativas)
                if not violacoes:
                    st.success("✅ Nenhuma violação encontrada com as regras personalizadas!")
                else:
                    st.error(f"⚠️ {len(violacoes)} violação(ões) encontrada(s).")
                    df_v = pd.DataFrame(violacoes)
                    # Destaca por severidade
                    def _highlight_sev(row):
                        cores = {"Crítico": "background-color:#fee2e2",
                                 "Alerta": "background-color:#fef9c3",
                                 "Informativo": "background-color:#dbeafe"}
                        return [cores.get(row["Severidade"], "")] * len(row)
                    st.dataframe(df_v.style.apply(_highlight_sev, axis=1),
                                 use_container_width=True, hide_index=True)
                    st.download_button(
                        "⬇️ Exportar Violações CSV",
                        df_v.to_csv(index=False, sep=";", encoding="utf-8-sig").encode("utf-8-sig"),
                        f"regras_custom_violacoes_{datetime.now().strftime('%Y%m%d_%H%M')}.csv",
                        "text/csv"
                    )
                    registrar_log(TENANT_ID, st.session_state.get("usuario_email","?"),
                                  "Executou regras personalizadas",
                                  f"{len(violacoes)} violações em {len(regras_ativas)} regras")

# ── Log de Acesso (admin) ─────────────────────────────────────────────────────
elif menu == "📋 Log de Acesso":
    if PAPEL != "admin":
        st.error("Acesso restrito a administradores.")
        st.stop()
    st.header("📋 Log de Acesso — Auditoria LGPD")
    logs = buscar_log_acesso(TENANT_ID, limite=200)
    if logs:
        df_log = pd.DataFrame(logs).rename(columns={
            "usuario_email":"Usuário","acao":"Ação","detalhe":"Detalhe","criado_em":"Data/Hora"
        })
        usuarios_log = ["Todos"] + sorted(df_log["Usuário"].unique().tolist())
        sel = st.selectbox("Filtrar por usuário:", usuarios_log)
        if sel != "Todos":
            df_log = df_log[df_log["Usuário"] == sel]
        st.dataframe(df_log, use_container_width=True)
        st.download_button("⬇️ Exportar CSV",
            df_log.to_csv(index=False).encode("utf-8"),
            f"log_acesso_{datetime.now().strftime('%Y%m%d')}.csv", "text/csv")
    else:
        st.info("Nenhum evento registrado ainda.")

# ── Cruzamento XML ─────────────────────────────────────────────────────────────
elif dados and menu == "🔌 Cruzamento XML":
    st.header("🔌 Cruzamento SPED vs XML")
    if not HAS_CRUZADOR:
        st.error("Módulo cruzador_xml.py não disponível.")
    else:
        st.markdown(f"NFes no SPED: **{len(dados['notas_sped'])}**")
        zip_up = st.file_uploader("Upload ZIP com XMLs", type="zip")
        if zip_up:
            with st.spinner("Lendo XMLs..."):
                notas_xml, _, erro = processar_zip_xml(zip_up.getvalue())
                if erro:
                    st.error(erro)
                else:
                    r = cruzar_sped_vs_xml(dados["notas_sped"], notas_xml)
                    c1, c2, c3 = st.columns(3)
                    c1.metric("XMLs Lidos", r["total_xml"])
                    c2.metric("Validados",  r["validadas_sucesso"])
                    faltam  = len(r["faltam_no_sped"])
                    diverg  = len(r["divergencias_valor"])
                    c3.metric("Omissões/Divergências", faltam + diverg,
                              delta="Risco" if (faltam+diverg)>0 else None, delta_color="inverse")
                    if faltam > 0:
                        st.error(f"🚨 {faltam} notas no ZIP ausentes no SPED!")
                        st.dataframe(pd.DataFrame(r["faltam_no_sped"]), use_container_width=True)
                    if diverg > 0:
                        st.warning(f"⚠️ {diverg} notas com valores divergentes.")
                        st.dataframe(pd.DataFrame(r["divergencias_valor"]), use_container_width=True)
                    if faltam == 0 and diverg == 0:
                        st.success("🏆 Todos os XMLs validados com sucesso.")

# ── Reforma Tributária ────────────────────────────────────────────────────────
elif dados and menu == "📊 Reforma Tributária":
    st.header("📊 Simulador — Reforma Tributária | LC 214/2025")
    st.caption("Alíquotas de referência: CBS 8,8% · IBS 17,7% · IVA pleno 26,5% — com reduções por NCM conforme Anexos I a V")

    tab_geral, tab_ncm, tab_cronograma = st.tabs([
        "📊 Visão Geral", "🏷️ Breakdown por NCM", "📅 Cronograma 2026–2033"
    ])

    with tab_geral:
        if dados.get("c190"):
            df_r = pd.DataFrame(dados["c190"])
            base  = float(df_r["Valor"].sum())
            icms  = float(df_r["ICMS"].sum())

            # Calcula CBS/IBS usando NCM quando disponível, ou flat
            # CORREÇÃO: média simples por produto (cada NCM tem peso 1).
            # Para ponderação real seria necessário cruzar NCM×valor do C170,
            # mas C190 não tem granularidade por item — usamos média simples como proxy.
            mapa_ncm = dados.get("mapa_ncm", {})
            if mapa_ncm:
                cats = [buscar_categoria_ncm(ncm) for ncm in mapa_ncm.values()]
                n = len(cats)
                cbs_rate = sum(c["cbs_aliq"] for c in cats) / n if n else _CBS_BASE
                ibs_rate = sum(c["ibs_aliq"] for c in cats) / n if n else _IBS_BASE
                iva_rate = sum(c["iva_aliq"] for c in cats) / n if n else _IVA_BASE
                st.caption(f"ℹ️ Alíquotas calculadas como média simples de {n} NCM(s) cadastrados. "
                           "Para simulação precisa, use a aba 'Breakdown por NCM'.")
            else:
                cbs_rate, ibs_rate, iva_rate = _CBS_BASE, _IBS_BASE, _IVA_BASE
                st.caption("ℹ️ Nenhum NCM encontrado no SPED — usando alíquotas plenas de referência.")

            cbs  = base * cbs_rate
            ibs  = base * ibs_rate
            iva  = base * iva_rate
            diff = iva - icms
            perc = (diff / icms * 100) if icms > 0 else 0

            st.markdown("**🧪 Fase 1 — 2026/2027 (CBS + IBS coexistem com ICMS):**")
            c1,c2,c3,c4 = st.columns(4)
            c1.metric("Base de Cálculo Total", f"R$ {base:,.2f}")
            c2.metric(f"CBS ({cbs_rate*100:.1f}%)", f"R$ {cbs:,.2f}",
                      help="Contribuição sobre Bens e Serviços — Receita Federal")
            c3.metric(f"IBS ({ibs_rate*100:.1f}%)", f"R$ {ibs:,.2f}",
                      help="Imposto sobre Bens e Serviços — Estados + Municípios")
            c4.metric("CBS + IBS (2026)", f"R$ {cbs+ibs:,.2f}")

            st.markdown("**🔮 Fase Final — 2033 (IVA Dual pleno, ICMS extinto):**")
            c1,c2,c3 = st.columns(3)
            c1.metric("ICMS Atual (a extinguir)", f"R$ {icms:,.2f}")
            c2.metric(f"IVA Dual ({iva_rate*100:.1f}%)", f"R$ {iva:,.2f}")
            c3.metric("Impacto vs ICMS atual", f"R$ {diff:,.2f}", delta=f"{perc:+.1f}%",
                      delta_color="inverse" if diff > 0 else "normal")

            # Bloco D — serviços de transporte
            vl_icms_frete = dados.get("vl_icms_servicos_d190", 0.0)
            vl_base_frete = dados.get("vl_doc_servicos_d100", 0.0)
            if vl_icms_frete > 0 or vl_base_frete > 0:
                st.divider()
                st.markdown("**🚚 Serviços de Transporte (CT-e — Bloco D):**")
                cf1, cf2, cf3 = st.columns(3)
                cf1.metric("ICMS Frete Atual", f"R$ {vl_icms_frete:,.2f}")
                # Fix G: CBS usa VL_DOC (base real) não ICMS; redução 60% na BC — LC 214 art. 9º §3º
                cbs_frete = vl_base_frete * (1 - 0.60) * _CBS_BASE
                cf2.metric("CBS Frete (60% red.)", f"R$ {cbs_frete:,.2f}",
                            help=f"Base: R$ {vl_base_frete:,.2f} (VL_DOC CT-e) × 40% × 8,8% — LC 214 art. 9º §3º")
                cf3.metric("CT-e processados", dados.get("total_cte", 0))
        else:
            st.warning("Sem dados C190 para simulação.")

        if HAS_REFORMA:
            laudo = dados.get("laudo_reforma_2026", {})
            if laudo and "conformidade" in laudo:
                st.divider()
                c1,c2 = st.columns(2)
                c1.metric("Score Compliance 2026", f"{laudo['conformidade']['score']}/100")
                c2.metric("Erros Transição", laudo.get("totalizadores",{}).get("total_erros",0))

    with tab_ncm:
        st.subheader("🏷️ Breakdown de Carga Tributária por NCM")
        st.caption("Alíquotas individuais por produto conforme Anexos I-V da LC 214/2025")

        mapa_ncm = dados.get("mapa_ncm", {})
        if not mapa_ncm:
            st.warning("Sem produtos (0200) no SPED para calcular por NCM.")
        else:
            # Monta tabela de produtos × alíquotas
            linhas_ncm = []
            for cod_item, ncm in mapa_ncm.items():
                cat = buscar_categoria_ncm(ncm)
                linhas_ncm.append({
                    "Produto": cod_item,
                    "NCM": ncm,
                    "Categoria": cat["nome"],
                    "Isento": "✅ Zero" if cat["isento"] else "",
                    "Redução LC 214": f"{cat['reducao']*100:.0f}%",
                    "CBS efetiva": f"{cat['cbs_aliq']*100:.2f}%",
                    "IBS efetiva": f"{cat['ibs_aliq']*100:.2f}%",
                    "IVA efetivo": f"{cat['iva_aliq']*100:.2f}%",
                    "Obs.": cat["obs"],
                })
            df_ncm = pd.DataFrame(linhas_ncm)

            # Filtro por categoria
            cats_disponiveis = sorted(df_ncm["Categoria"].unique())
            cat_sel = st.multiselect("Filtrar categorias:", cats_disponiveis,
                                     default=cats_disponiveis[:5] if len(cats_disponiveis) > 5 else cats_disponiveis)
            if cat_sel:
                df_ncm_f = df_ncm[df_ncm["Categoria"].isin(cat_sel)]
            else:
                df_ncm_f = df_ncm

            st.dataframe(df_ncm_f, use_container_width=True, hide_index=True)

            # Gráfico de alíquotas por categoria
            df_cat_agg = (df_ncm.groupby("Categoria")
                          .agg(Produtos=("Produto","count"),
                               IVA_Efetivo=("IVA efetivo", lambda x: x.str.replace("%","").astype(float).mean()))
                          .reset_index()
                          .sort_values("IVA_Efetivo"))
            fig_ncm = px.bar(df_cat_agg, x="Categoria", y="IVA_Efetivo", color="IVA_Efetivo",
                             color_continuous_scale=["#22C55E","#F59E0B","#EF4444"],
                             range_color=[0, 26.5],
                             title="Alíquota IVA Efetiva Média por Categoria de Produto",
                             labels={"IVA_Efetivo": "IVA Efetivo (%)", "Categoria": ""},
                             text_auto=".1f")
            fig_ncm.update_layout(coloraxis_showscale=False, xaxis_tickangle=-30)
            fig_ncm.add_hline(y=26.5, line_dash="dash", line_color="#EF4444",
                              annotation_text="IVA pleno 26,5%")
            st.plotly_chart(fig_ncm, use_container_width=True)

            # Distribuição: isentos vs. reduzidos vs. plenos
            n_isento  = (df_ncm["Redução LC 214"] == "100%").sum()
            n_reduzido= ((df_ncm["Redução LC 214"] != "0%") & (df_ncm["Redução LC 214"] != "100%")).sum()
            n_pleno   = (df_ncm["Redução LC 214"] == "0%").sum()
            fig_pie = px.pie(
                values=[n_isento, n_reduzido, n_pleno],
                names=["Alíq. Zero (Cesta Básica)", "Reduzido (parcial)", "Alíquota Plena"],
                color_discrete_sequence=["#22C55E","#F59E0B","#EF4444"],
                title="Distribuição de Produtos por Regime LC 214/2025",
            )
            st.plotly_chart(fig_pie, use_container_width=True)

            # Download
            csv_ncm = df_ncm.to_csv(index=False, sep=";", encoding="utf-8-sig").encode("utf-8-sig")
            st.download_button("⬇️ Exportar tabela NCM × Alíquota", csv_ncm,
                               f"ncm_aliquota_reforma_{datetime.now().strftime('%Y%m%d')}.csv", "text/csv")

    with tab_cronograma:
        st.subheader("📅 Cronograma de Transição 2026–2033")
        cronograma = pd.DataFrame([
            {"Ano": 2026, "CBS": "0,9%", "IBS": "0,1%", "ICMS": "mantido", "IS": "0,1%",
             "Fase": "🧪 Teste", "Descrição": "CBS e IBS surgem com alíquotas reduzidas. ICMS continua integral."},
            {"Ano": 2027, "CBS": "1,8%", "IBS": "0,2%", "ICMS": "mantido", "IS": "0,2%",
             "Fase": "🔄 Transição I", "Descrição": "Aumento gradual de CBS e IBS. PIS/COFINS extintos."},
            {"Ano": 2028, "CBS": "3,6%", "IBS": "0,4%", "ICMS": "90%", "IS": "0,4%",
             "Fase": "🔄 Transição II", "Descrição": "ICMS começa a ser reduzido. CBS cresce."},
            {"Ano": 2029, "CBS": "5,4%", "IBS": "4,0%", "ICMS": "80%", "IS": "0,6%",
             "Fase": "🔄 Transição III", "Descrição": "IBS ganha peso. ICMS reduzido a 80%."},
            {"Ano": 2030, "CBS": "7,2%", "IBS": "8,8%", "ICMS": "60%", "IS": "0,8%",
             "Fase": "🔄 Transição IV", "Descrição": "IBS supera ICMS. Migração acelerada."},
            {"Ano": 2031, "CBS": "8,0%", "IBS": "13,3%", "ICMS": "40%", "IS": "1,0%",
             "Fase": "🔄 Transição V", "Descrição": "ICMS reduzido a 40%. IBS quase pleno."},
            {"Ano": 2032, "CBS": "8,4%", "IBS": "15,5%", "ICMS": "20%", "IS": "1,0%",
             "Fase": "🔄 Transição VI", "Descrição": "ICMS reduzido a 20%. Último ano de coexistência."},
            {"Ano": 2033, "CBS": "8,8%", "IBS": "17,7%", "ICMS": "EXTINTO", "IS": "1,0%",
             "Fase": "✅ Pleno", "Descrição": "ICMS, ISS e PIS/COFINS extintos. IVA Dual pleno em vigor."},
        ])
        st.dataframe(cronograma, use_container_width=True, hide_index=True)

        # Gráfico de evolução das alíquotas
        anos = [2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033]
        cbs_ev  = [0.9, 1.8, 3.6, 5.4, 7.2, 8.0, 8.4, 8.8]
        ibs_ev  = [0.1, 0.2, 0.4, 4.0, 8.8, 13.3, 15.5, 17.7]
        icms_ev = [17.0, 17.0, 15.3, 13.6, 10.2, 6.8, 3.4, 0.0]  # 17% médio → extinção
        fig_ev = px.area(
            pd.DataFrame({"Ano": anos*3,
                          "Alíquota (%)": cbs_ev+ibs_ev+icms_ev,
                          "Tributo": ["CBS"]*8 + ["IBS"]*8 + ["ICMS"]*8}),
            x="Ano", y="Alíquota (%)", color="Tributo",
            color_discrete_map={"CBS":"#3B82F6","IBS":"#8B5CF6","ICMS":"#EF4444"},
            title="Transição das Alíquotas 2026–2033 (alíquota média referência)"
        )
        fig_ev.update_layout(xaxis=dict(tickmode="array", tickvals=anos))
        st.plotly_chart(fig_ev, use_container_width=True)

        if dados.get("c190"):
            base_total = float(pd.DataFrame(dados["c190"])["Valor"].sum())
            st.markdown("**💰 Projeção de carga tributária para sua empresa:**")
            # Fator de redução do ICMS por ano de transição (LC 214 art. 121-130)
            _icms_reducao_por_ano = {
                2026: 0.0,   # mantido integral
                2027: 0.0,   # mantido integral (PIS/COFINS extintos)
                2028: 0.10,  # reduzido 10%
                2029: 0.20,  # reduzido 20%
                2030: 0.40,  # reduzido 40%
                2031: 0.60,  # reduzido 60%
                2032: 0.80,  # reduzido 80%
                2033: 1.0,   # extinto
            }
            proj = []
            for row in cronograma.itertuples():
                try:
                    cbs_r = float(str(row.CBS).replace("%","").replace(",",".")) / 100
                    ibs_r = float(str(row.IBS).replace("%","").replace(",",".")) / 100
                    if row.ICMS == "EXTINTO":
                        icms_r = 0.0
                    else:
                        reducao = _icms_reducao_por_ano.get(row.Ano, 0.0)
                        icms_r = 0.17 * (1 - reducao)   # 17% alíquota média referência
                    proj.append({"Ano": row.Ano,
                                 "CBS (R$)": base_total * cbs_r,
                                 "IBS (R$)": base_total * ibs_r,
                                 "ICMS ref (R$)": base_total * icms_r})
                except Exception:
                    pass
            if proj:
                df_proj = pd.DataFrame(proj)
                fig_proj = px.bar(df_proj, x="Ano",
                                  y=["CBS (R$)", "IBS (R$)", "ICMS ref (R$)"],
                                  barmode="stack",
                                  color_discrete_map={"CBS (R$)":"#3B82F6","IBS (R$)":"#8B5CF6","ICMS ref (R$)":"#EF4444"},
                                  title=f"Projeção de Carga Tributária — Base R$ {base_total:,.0f}")
                st.plotly_chart(fig_proj, use_container_width=True)

# ── Histórico & Score ─────────────────────────────────────────────────────────
elif menu == "📈 Histórico & Score":
    st.header("📈 Histórico & Score de Risco")
    if dados:
        score, eg, eo = calcular_score(dados)
        status_score = ("Excelente" if score>=90 else "Bom" if score>=75 else
                        "Atenção" if score>=60 else "Risco Moderado" if score>=40 else "Alto Risco")
        c1,c2,c3,c4 = st.columns(4)
        c1.metric("Score Fiscal", f"{score}/100", status_score)
        c2.metric("Erros Graves", eg)
        c3.metric("Erros Operacionais", eo)
        c4.metric("Divergência ICMS",
                  f"R$ {abs(dados.get('vl_icms_saidas_c190',0)-dados.get('vl_tot_debitos_e110',0)):,.2f}")
        st.divider()
        hist = buscar_historico(TENANT_ID, dados.get("cnpj",""))
        if len(hist) > 1:
            df_h = pd.DataFrame(hist)[::-1].reset_index(drop=True)
            fig = px.line(df_h, x="periodo", y="score", markers=True,
                          title="Evolução do Score Fiscal", color_discrete_sequence=["#4F46E5"])
            fig.add_hline(y=75, line_dash="dash", line_color="orange", annotation_text="Limite Atenção")
            fig.add_hline(y=60, line_dash="dash", line_color="red",    annotation_text="Limite Risco")
            fig.update_layout(yaxis_range=[0,100])
            st.plotly_chart(fig, use_container_width=True)
            ca, cb = st.columns(2)
            with ca:
                st.plotly_chart(px.bar(df_h, x="periodo", y="erros_graves",
                                       title="Erros Graves por Período",
                                       color_discrete_sequence=["#EF4444"]),
                                use_container_width=True)
            with cb:
                st.plotly_chart(px.bar(df_h, x="periodo", y="total_erros",
                                       title="Total de Erros por Período",
                                       color_discrete_sequence=["#F59E0B"]),
                                use_container_width=True)
            st.dataframe(df_h[["periodo","score","total_erros","erros_graves","divergencia_icms","criado_em"]],
                         use_container_width=True)
            scores = df_h["score"].tolist()
            if len(scores) >= 2:
                delta = scores[-1] - scores[-2]
                if delta < -5:
                    st.warning(f"⚠️ Score caiu {abs(delta)} pts em relação ao período anterior.")
                elif delta > 5:
                    st.success(f"✅ Score subiu {delta} pts em relação ao período anterior.")
        else:
            st.info("Processe mais de um período para ver a evolução.")
    else:
        st.info("Carregue um SPED para ver o histórico desta empresa.")

# ── Gestão de Usuários (admin) ────────────────────────────────────────────────
elif menu == "👥 Usuários & Empresa":
    if PAPEL != "admin":
        st.error("Acesso restrito a administradores.")
        st.stop()
    st.header("👥 Gestão de Usuários")

    limite_usuarios = PLANO_INFO["usuarios"]
    usuarios = listar_usuarios(TENANT_ID)
    st.metric("Usuários ativos", f"{sum(1 for u in usuarios if u['ativo'])}/{limite_usuarios}")

    st.subheader("Convidar novo usuário")
    plano_ok = sum(1 for u in usuarios if u["ativo"]) < limite_usuarios
    if not plano_ok:
        st.warning(f"Limite de {limite_usuarios} usuários atingido. Faça upgrade para adicionar mais.")
    else:
        with st.form("form_invite"):
            col1, col2 = st.columns(2)
            with col1:
                inv_email = st.text_input("E-mail")
                inv_nome  = st.text_input("Nome")
            with col2:
                inv_papel = st.selectbox("Papel", PAPEIS, format_func=lambda x: PAPEIS_LABEL[x])
            if st.form_submit_button("Criar usuário"):
                if inv_email and inv_nome:
                    uid, senha_tmp = criar_usuario(TENANT_ID, inv_email, inv_nome, inv_papel)
                    st.success(f"Usuário criado! Senha temporária: **{senha_tmp}** (comunique ao usuário para trocar.)")
                else:
                    st.error("Preencha e-mail e nome.")

    st.divider()
    st.subheader("Usuários do tenant")
    if usuarios:
        df_usr = pd.DataFrame(usuarios)
        _cols_usr = [c for c in ["email","nome","papel","ativo","ultimo_login","criado_em"] if c in df_usr.columns]
        df_usr = df_usr[_cols_usr]
        df_usr["papel"] = df_usr["papel"].map(PAPEIS_LABEL)
        df_usr["ativo"] = df_usr["ativo"].map({1:"✅ Ativo", 0:"🚫 Inativo"})
        st.dataframe(df_usr, use_container_width=True)
    else:
        st.info("Nenhum usuário cadastrado.")

    st.divider()
    st.subheader("Desativar usuário")
    emails_ativos = [u["email"] for u in usuarios if u["ativo"] and u["email"] != USER["email"]]
    if emails_ativos:
        sel_email = st.selectbox("Selecionar usuário:", emails_ativos)
        if st.button("Desativar", type="primary"):
            uid_sel = next(u["id"] for u in usuarios if u["email"] == sel_email)
            desativar_usuario(uid_sel, TENANT_ID)
            st.success(f"Usuário {sel_email} desativado.")
            st.rerun()
    else:
        st.info("Nenhum outro usuário ativo.")

    st.divider()
    st.subheader("Trocar minha senha")
    with st.form("form_senha"):
        nova1 = st.text_input("Nova senha", type="password")
        nova2 = st.text_input("Confirmar senha", type="password")
        if st.form_submit_button("Salvar"):
            if nova1 != nova2:
                st.error("Senhas não coincidem.")
            elif len(nova1) < 8:
                st.error("Senha mínima de 8 caracteres.")
            else:
                alterar_senha(USER_ID, nova1)
                st.success("Senha alterada.")

    st.divider()
    st.subheader("Empresas cadastradas")
    empresas = listar_empresas_tenant(TENANT_ID)
    if empresas:
        st.dataframe(pd.DataFrame(empresas)[["nome","cnpj","uf","criado_em"]], use_container_width=True)
    else:
        st.info("Nenhuma empresa processada ainda.")

# ── Conta & Plano ─────────────────────────────────────────────────────────────
elif menu == "⚙️ Conta & Plano":
    if PAPEL != "admin":
        st.error("Acesso restrito a administradores.")
        st.stop()
    st.header("⚙️ Conta & Plano")

    st.subheader("Plano atual")
    pnome = PLANO_INFO["nome"]
    col1, col2, col3 = st.columns(3)
    col1.metric("Plano",             PLANO_INFO["label"])
    col2.metric("SPEDs/mês",         PLANO_INFO["speds_mes"])
    col3.metric("Usuários permitidos", PLANO_INFO["usuarios"])

    if PLANO_INFO.get("trial_restante") is not None:
        st.warning(f"⏳ Trial expira em {PLANO_INFO['trial_restante']} dias.")

    st.divider()
    st.subheader("Comparativo de planos")
    planos_df = pd.DataFrame([
        {"Plano": "Trial (14 dias)",  "SPEDs/mês": 5,   "Usuários": 2,   "Histórico": "3 meses",  "Preço": "Grátis"},
        {"Plano": "Starter",          "SPEDs/mês": 20,  "Usuários": 3,   "Histórico": "6 meses",  "Preço": "R$ 297/mês"},
        {"Plano": "Profissional",     "SPEDs/mês": 100, "Usuários": 10,  "Histórico": "24 meses", "Preço": "R$ 797/mês"},
        {"Plano": "Enterprise",       "SPEDs/mês": "∞", "Usuários": "∞", "Histórico": "Ilimitado","Preço": "R$ 1.997/mês"},
    ])
    st.dataframe(planos_df, use_container_width=True, hide_index=True)
    st.info("Para upgrade, entre em contato: contato@auditax.com.br")

    st.divider()
    st.subheader("Uso este mês")
    _, msg_q = verificar_quota(TENANT_ID, PLANO_INFO)
    st.info(msg_q)

    # ── Personalização do Laudo PDF ───────────────────────────────────────────
    st.divider()
    st.subheader("🎨 Personalização do Laudo PDF")
    st.caption("Configure logo e cor para os laudos gerados pelo seu escritório/empresa.")
    col_logo, col_cor = st.columns([2, 1])
    with col_logo:
        logo_up = st.file_uploader("Logo do Escritório (PNG/JPG, max 500 KB)",
                                   type=["png", "jpg", "jpeg"], key="logo_uploader")
        if logo_up:
            if logo_up.size > 500_000:
                st.error("Arquivo muito grande. Use até 500 KB.")
            else:
                st.session_state["logo_pdf_bytes"] = logo_up.read()
                st.success("✅ Logo carregado! Será usado no próximo PDF gerado.")
                st.image(st.session_state["logo_pdf_bytes"], width=180)
        elif st.session_state.get("logo_pdf_bytes"):
            st.image(st.session_state["logo_pdf_bytes"], width=180, caption="Logo atual")
            if st.button("🗑️ Remover logo"):
                st.session_state["logo_pdf_bytes"] = None
                st.rerun()
    with col_cor:
        cor_atual = st.session_state.get("cor_pdf", "#1E3A5F")
        nova_cor  = st.color_picker("Cor primária do PDF", value=cor_atual)
        if nova_cor != cor_atual:
            st.session_state["cor_pdf"] = nova_cor
        st.caption(f"Cor selecionada: `{st.session_state.get('cor_pdf','#1E3A5F')}`")
