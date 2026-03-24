import streamlit as st
import pandas as pd
import io
import plotly.express as px
import datetime

# --- CONFIGURAÇÃO DA PÁGINA ---
st.set_page_config(page_title="Auditax 360º Pro", layout="wide", page_icon="🛡️")

# Estilo CSS para melhorar a visualização
st.markdown("""
<style>
    .metric-card {background-color: #f0f2f6; border-radius: 10px; padding: 20px;}
    .stTabs [data-baseweb="tab-list"] {gap: 10px;}
    .stTabs [data-baseweb="tab"] {height: 50px; white-space: pre-wrap; border-radius: 4px 4px 0px 0px;}
</style>
""", unsafe_allow_html=True)

# --- 1. SISTEMA DE SEGURANÇA (LOGIN) ---
def check_password():
    """Retorna True se o usuário acertar a senha."""
    if "password_correct" not in st.session_state:
        st.session_state["password_correct"] = False

    if st.session_state["password_correct"]:
        return True

    col1, col2, col3 = st.columns([1,2,1])
    with col2:
        st.markdown("### 🔒 Acesso Restrito - Auditax 360º")
        st.info("Digite a senha para acessar o painel de auditoria.")
        pwd = st.text_input("Senha de Acesso:", type="password")
        
        # --- DEFINA SUA SENHA AQUI EMBAIXO ---
        if st.button("Entrar no Sistema"):
            if pwd == "Fiscal123":  # <--- SENHA
                st.session_state["password_correct"] = True
                st.rerun()
            else:
                st.error("Senha incorreta. Tente novamente.")
    return False

if not check_password():
    st.stop()

# --- 2. FUNÇÕES DE PROCESSAMENTO ---

def validar_estrutura(linhas):
    """Verifica erros de pipes no início e fim."""
    erros = []
    for i, linha in enumerate(linhas):
        linha = linha.strip()
        if not linha: continue
        
        # Regra: Começa e termina com pipe
        if not linha.startswith('|') or not linha.endswith('|'):
            erros.append(['Estrutura', i+1, 'N/A', 'Linha sem delimitador "|" (Pipe)'])
            
    return erros

def corrigir_arquivo_automaticamente(linhas):
    """Conserta pipes e remove linhas vazias."""
    linhas_corrigidas = []
    log_correcoes = []
    
    for i, linha in enumerate(linhas):
        linha_original = linha.strip()
        
        if not linha_original:
            continue # Remove vazios
            
        modificou = False
        temp_linha = linha_original
        
        if not temp_linha.startswith('|'):
            temp_linha = '|' + temp_linha
            modificou = True
            
        if not temp_linha.endswith('|'):
            temp_linha = temp_linha + '|'
            modificou = True
            
        if modificou:
            log_correcoes.append(f"Linha {i+1}: Pipes corrigidos.")
            
        linhas_corrigidas.append(temp_linha + '\r\n')
        
    return linhas_corrigidas, log_correcoes

def processar_dados_gerenciais(linhas):
    """Lê o bloco C190 para gerar gráficos."""
    dados = []
    for linha in linhas:
        if linha.startswith('|C190|'):
            campos = linha.split('|')
            try:
                # C190: [2] CST, [3] CFOP, [5] Valor Opr, [6] BC ICMS, [7] Vlr ICMS
                dados.append({
                    'CST': campos[2],
                    'CFOP': campos[3],
                    'Valor_Contabil': float(campos[5].replace(',', '.')),
                    'Valor_ICMS': float(campos[7].replace(',', '.'))
                })
            except: pass
    return pd.DataFrame(dados)

def auditoria_detalhada(linhas):
    """Verifica Orfãos (Integridade) e Estoque Negativo."""
    prod_cadastrados = set()
    prod_usados = set()
    estoque = {} # {cod_item: saldo}
    erros_integ = []
    erros_estoque = []

    for i, linha in enumerate(linhas):
        if not linha.startswith('|'): continue
        campos = linha.split('|')
        reg = campos[1]
        lin_num = i + 1
        
        # Cadastro 0200
        if reg == '0200':
            prod_cadastrados.add(campos[2])
            
        # Movimentação C170
        elif reg == 'C170':
            try:
                cod = campos[3]
                prod_usados.add(cod)
                
                qtd = float(campos[5].replace(',', '.'))
                cfop = campos[11]
                
                # Inicializa saldo
                if cod not in estoque: estoque[cod] = 0.0
                
                # Lógica Kardex Simples
                if cfop[0] in ['1','2','3']: # Entradas
                    estoque[cod] += qtd
                elif cfop[0] in ['5','6','7']: # Saídas
                    estoque[cod] -= qtd
                
                # Verifica furo de estoque
                if estoque[cod] < 0:
                    erros_estoque.append([lin_num, cod, cfop, estoque[cod], 'Saldo Negativo'])
            except: pass

    # Verifica quem foi usado mas não tem cadastro
    orfaos = prod_usados - prod_cadastrados
    for p in orfaos:
        erros_integ.append(['N/A', p, 'Produto movimentado sem registro 0200'])
        
    return erros_integ, erros_estoque

# --- 3. INTERFACE DO USUÁRIO ---

st.title("📊 Auditax 360º - Solução Fiscal Integrada")
st.markdown("Importe seu arquivo SPED (.txt) para validação, auditoria e correção automática.")
st.divider()

uploaded_file = st.file_uploader("Arraste seu arquivo aqui", type="txt")

if uploaded_file is not None:
    # Ler o arquivo
    stringio = io.StringIO(uploaded_file.getvalue().decode("latin-1"))
    linhas = stringio.readlines()
    
    st.info("Arquivo carregado. Processando dados...")
    
    # Executar Processamentos
    df_dash = processar_dados_gerenciais(linhas)
    lista_estutura = validar_estrutura(linhas)
    lista_integ, lista_estoque = auditoria_detalhada(linhas)
    
    # Criar Abas
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "📈 Dashboard Gerencial", 
        "🛠️ Correção Automática", 
        "🏗️ Erros de Estrutura", 
        "🔗 Integridade (Orfãos)", 
        "📦 Estoque (Kardex)"
    ])
    
    # --- ABA 1: DASHBOARD ---
    with tab1:
        st.subheader("Visão Geral da Apuração (Base C190)")
        if not df_dash.empty:
            total_venda = df_dash['Valor_Contabil'].sum()
            total_icms = df_dash['Valor_ICMS'].sum()
            
            c1, c2, c3 = st.columns(3)
            c1.metric("Valor Contábil Total", f"R$ {total_venda:,.2f}")
            c2.metric("Total ICMS", f"R$ {total_icms:,.2f}")
            c3.metric("Carga Tributária Média", f"{((total_icms/total_venda)*100):.2f}%" if total_venda > 0 else "0%")
            
            st.divider()
            
            g1, g2 = st.columns(2)
            with g1:
                st.markdown("**Top CFOPs (Valor)**")
                fig1 = px.pie(df_dash, values='Valor_Contabil', names='CFOP', hole=0.4)
                st.plotly_chart(fig1, use_container_width=True)
            with g2:
                st.markdown("**ICMS por Situação Tributária (CST)**")
                fig2 = px.bar(df_dash.groupby('CST')['Valor_ICMS'].sum().reset_index(), x='CST', y='Valor_ICMS')
                st.plotly_chart(fig2, use_container_width=True)
        else:
            st.warning("Não há dados no registro C190 para gerar gráficos.")

    # --- ABA 2: CORREÇÃO AUTOMÁTICA ---
    with tab2:
        st.subheader("Saneamento de Arquivo")
        st.markdown("Esta ferramenta corrige pipes (`|`) faltantes e remove linhas vazias.")
        
        if st.button("🔧 Corrigir Arquivo e Gerar Novo TXT"):
            txt_novo, logs = corrigir_arquivo_automaticamente(linhas)
            if logs:
                st.success(f"{len(logs)} correções aplicadas!")
                with st.expander("Ver lista de correções"):
                    st.write(logs)
                
                # Download
                st.download_button(
                    label="📥 Baixar TXT Corrigido",
                    data="".join(txt_novo).encode("latin-1"),
                    file_name="SPED_CORRIGIDO.txt",
                    mime="text/plain"
                )
            else:
                st.success("O arquivo já está estruturalmente perfeito!")

    # --- ABA 3: ESTRUTURA ---
    with tab3:
        if lista_estutura:
            st.error(f"{len(lista_estutura)} Erros Encontrados")
            st.dataframe(pd.DataFrame(lista_estutura, columns=['Tipo','Linha','Reg','Erro']), use_container_width=True)
        else:
            st.success("Nenhum erro de estrutura.")

    # --- ABA 4: INTEGRIDADE ---
    with tab4:
        if lista_integ:
            st.warning(f"{len(lista_integ)} Produtos sem Cadastro (0200)")
            st.dataframe(pd.DataFrame(lista_integ, columns=['Linha','Item','Erro']), use_container_width=True)
        else:
            st.success("Todos os produtos movimentados possuem cadastro.")

    # --- ABA 5: ESTOQUE ---
    with tab5:
        if lista_estoque:
            st.error(f"{len(lista_estoque)} Itens com Estoque Negativo")
            st.dataframe(pd.DataFrame(lista_estoque, columns=['Linha','Item','CFOP','Saldo','Status']), use_container_width=True)
        else:
            st.success("Nenhuma ocorrência de estoque negativo detectada.")
            
    # --- EXPORTAÇÃO GERAL ---
    st.divider()
    st.subheader("📥 Relatório Completo")
    
    buffer = io.BytesIO()
    with pd.ExcelWriter(buffer, engine='openpyxl') as writer:
        if lista_estutura: pd.DataFrame(lista_estutura).to_excel(writer, sheet_name='Estrutura')
        if lista_integ: pd.DataFrame(lista_integ).to_excel(writer, sheet_name='Integridade')
        if lista_estoque: pd.DataFrame(lista_estoque).to_excel(writer, sheet_name='Estoque')
        if not df_dash.empty: df_dash.to_excel(writer, sheet_name='Dados_Gerenciais')
        
    st.download_button(
        label="Baixar Relatório de Auditoria (Excel)",
        data=buffer,
        file_name="Relatorio_Auditoria_Completo.xlsx",
        mime="application/vnd.ms-excel"
    )
