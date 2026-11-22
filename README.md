# Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada bajo Rendimientos Crecientes

Código, certificados formales CEGIS-PWL auditados por aritmética de intervalos, figuras y manuscrito en Typst del **Artículo A**, construido como extensión independiente, auditable y autocontenida sobre *Minimum Viable Scale* de Milei y Reidel (octubre de 2026).

---

## Resultados principales certificados

1. **Afilamiento determinista y cascada completa de entrada ($46 \to 23 \to 9 \to 6 \to 4$):**
   - **Teorema 9\* (barrera afín analítica cerrada de 1 paso):** reduce la holgura de bloque de 2 pasos de Milei–Reidel de $\tau_H \le 46$ a $\tau_H \le 23$ períodos en $M = [0.10, 0.28)$ sin caja negra numérica.
   - **Proposición 1\* (corregida) y testigo afilado en $M_0 = [0.05, 0.10)$:** corrige la condición analítica real de signo negativo en $\partial u/\partial \eta$ ($c < 1 - L = 0.25$) y afila el plazo de salida en $M_0$ hasta $\tau_{.1} \le 9$ (holgura $+0.5253$ frente a MR-Tabla 4), auditado contra el techo CEGIS $\Psi(0.10) = -35.1667$ con derivada certificada $\inf_{M_0} \Psi' \ge 91.23 > 6.4234$.
   - **Síntesis adaptativa CEGIS-PWL (`Caso 1`):** comprime una barrera log-PWL certificada $B_\theta$ de **22 nodos** en $M$ ($d_{\text{ub,iv}} = -0.000300$, 58\,077 hojas 3D auditadas), reduciendo la cota garantizada a **$T_\theta = 9$** con MR-Tabla 4 y a **$T_{\text{full}} = 6$** con la tripleta CEGIS-LP $(\Psi, W, B_\theta)$ (frente a $\tau_H^{\text{DP}} = 9$ y $\tau_H^{\text{VFI}} = 4$).
   - **Proposición 1\*\*:** certificación analítica en intervalos `Decimal` de 50 dígitos y Wronskiano de las salidas adversas en $M$ ($l_0 = 0.44$) y $H_1 = [0.28, 0.80)$ ($l_0 = 0.60$ y $l_0 = 0.57$), verificando interioridad estricta del ocio $\omega^* < 1$ y la rama de salida $s = 0$ de `(F.20)`.

2. **Resolución asintótica de la Nota al pie 1 (Teorema 3\* y Corolario 2\*):**
   - Convergencia uniforme $A^2 S_A^{\text{fix}}(1) \to (\delta/c_K)^2 = 0.000800$ y extensión al régimen de paciencia débil $\beta\theta > 1$ ($\beta = 0.90$, $\beta\theta = 1.35 > 1$).
   - Verificación numérica en escala $\log k$ hasta $A = 10^8$: se confirma $0 < \Delta W_A^{\pi^+} \le \Delta W_A^+ \to 0^+$ a ritmo polilogarítmico $\Theta(\beta^{T_{\text{esc}}(A)})$ ($T_{\text{esc}}(10^8) = 126$, $\beta^{126} = 0.02154 \gg A^{-1} = 10^{-8}$), $L_{\text{endo}} \to L_{\text{ss}} = 7/9 \approx 0.7778$, y $\Delta W_A^- = O(A^{-1})$.

3. **Supervivencia estocástica certificada de Doob (`Caso 2`, `Caso 3` y `Caso 4`):**
   - **Caso 2 (riesgo de ruina continuo sobre $p \in [0\%, 2.0\%]$):** 60 bandas contiguas sobre $\tilde{\beta}_p \in [0.950502, 0.9701]$ con $d_{\text{ub,raw}} \le 0$ antes de desplazamientos; `B_cegis` sintetizada y auditada por intervalos en las **60/60 bandas** con plazo comprimido uniforme **$T^*_{\text{CEGIS}} \in \{5, 6\}$** (en la esquina $p = 2.0\%$, $T^*_{B_1}(2.0\%) = 93$ y **$T^*_{\text{CEGIS}}(2.0\%) = 5$**, supervivencia garantizada de Doob $90.4\%$).
   - **Caso 3 (Markov acoplado 2 estados $(G, B)$ hasta $p = 12\%$):** 64 certificados externos $(p \times 8\text{-}\beta)$ + auditoría continua en 32 subcajas 3D ($256$ pares $(s, p)$ certificados con `interval_check=True`, brecha uniforme de Doob $\varepsilon_0 \ge 0.0069$ —valor exacto `0.006905` en $p = 12.0\%$— y $m_{H_1,B,\text{iv}} > 0$ en todas las subcajas).
   - **Caso 4 (régimen $AK$ continuo por tramos):** transferencia automática con $\Psi_{AK}(0.28) = +243.4645$ ($W_{AK}(0.28) = +238.1434$), $T_{AK} = 4$ y $m_{H_2,[3.5,\infty),\text{iv}} = +59.7121$.

---

## Estructura del repositorio

```text
mvs-bellman-barriers/
├── pwl_model.py              # Representación exacta log-PWL y biyección con redes ReLU 1D
├── interval_audit.py         # Capa 1 Decimal (50 dígitos) + Capa 2 Numba IEEE-754 redondeo dirigido
├── rust_verifier/            # Acelerador nativo opcional en Rust (sin crates externos)
│   ├── Cargo.toml
│   ├── build.py              # Compila mvs_verifier.dll / libmvs_verifier.so/.dylib vía rustc
│   └── src/lib.rs            # Verificadores B&B + intervalos IEEE-754 (next_down/next_up)
├── cegis_verifier.py         # Interfaz dual Rust/Python + verificadores B&B y auditoría terminal
├── cegis_synth.py            # Motor Proposer-Verifier CEGIS-LP ralo (HiGHS) y barra de progreso
├── progress_bar.py           # Indicador de avance con tiempo transcurrido y ETA
├── cegis_certificates.json   # Certificados log-PWL exportados y auditados (Casos 1, 2, 3 y 4)
├── verify_article_a.py       # Reproducción y re-auditoría completa (Sec. 3, Sec. 4, Sec. 5, JSON 1-4)
├── generate_figures.py       # Genera fig1_barrier_es, fig2_scaling_es, fig3_stochastic_es (.svg/.png)
├── fig1_barrier_es.{svg,png}
├── fig2_scaling_es.{svg,png}
├── fig3_stochastic_es.{svg,png}
├── mvs_articulo_a_es.typ     # Fuente del manuscrito en Typst
├── mvs_articulo_a_es.pdf     # Manuscrito compilado en PDF (23 páginas)
└── requirements.txt
```

---

## Instalación y reproducibilidad

### 1. Dependencias Python
```bash
pip install -r requirements.txt
```

### 2. Acelerador nativo en Rust (opcional, fallback 100% Python disponible)
Si contás con `rustc` (>= 1.86, para `f64::next_down`/`next_up` en `std`), podés compilar el verificador B&B + intervalos sin dependencias externas:
```bash
python rust_verifier/build.py
```
El módulo `cegis_verifier.py` detecta automáticamente la librería compartida (`mvs_verifier.dll` / `libmvs_verifier.so` / `libmvs_verifier.dylib`). Para forzar el respaldo puro en Python/Numba + `Decimal` (50 dígitos), ejecutá con:
```bash
MVS_USE_RUST=0 python -u verify_article_a.py --full-audit
```

### 3. Verificación completa y generación de artefactos
```bash
# Verificación analítica/VFI estándar + spot-check de certificados JSON:
python -u verify_article_a.py

# Suite completa + auditoría exhaustiva del 100% de certificados (60 bandas Caso 2, 64 bandas Markov Caso 3, Casos 1 y 4):
python -u verify_article_a.py --full-audit

# Solo re-auditoría independiente de cegis_certificates.json (sin re-ejecutar VFI):
python -u verify_article_a.py --full-audit --audit-only

# Regeneración de figuras (.svg y .png a 300 dpi):
python -u generate_figures.py

# Compilación del manuscrito Typst:
python -c "import typst; typst.compile('mvs_articulo_a_es.typ', output='mvs_articulo_a_es.pdf')"

# Re-síntesis completa desde cero de los certificados CEGIS (Casos 1, 2, 3, 4):
python -u cegis_synth.py --all --seed 42
```

---

## Licencia
Distribuido bajo licencia MIT ([LICENSE](LICENSE)).
