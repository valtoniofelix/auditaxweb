# 🎈 Blank app template

A simple Streamlit app template for you to modify!

[![Open in Streamlit](https://static.streamlit.io/badges/streamlit_badge_black_white.svg)](https://blank-app-template.streamlit.app/)

### How to run it on your own machine

1. Install the requirements

requirements.txt
streamlit
supabase
2. Run the app

   ```
   $ streamlit import streamlit as st
from supabase import create_client

st.set_page_config(page_title="Auditax 360", layout="wide")

st.title("📊 Auditax 360")
st.caption("Auditoria fiscal automatizada")

url = st.secrets["SUPABASE_URL"]
key = st.secrets["SUPABASE_ANON_KEY"]

supabase = create_client(url, key)

st.success("✅ Conectado ao Supabase com sucesso!")run streamlit_app.py
   ```
