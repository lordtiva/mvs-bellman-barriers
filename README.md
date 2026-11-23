# Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada bajo Rendimientos Crecientes

Código, certificados formales **CEGIS-LP deterministas** auditados por aritmética de intervalos sin `libm`, figuras y manuscrito en Typst construidos como extensión independiente, auditable y autocontenida sobre *Minimum Viable Scale* de Milei y Reidel (octubre de 2026).

---

## Resultados principales certificados

1. **Afilamiento determinista, cadena no estacionaria y cierre casi hasta el punto de Skiba ($46 \to 23 \to 9 \to 5 \to 4$):**
   - **Teorema 1 (afilamiento del Teorema 9 de MR — barrera afín analítica cerrada de 1 paso):** reduce la holgura de bloque de 2 pasos de Milei–Reidel de $\tau_H \le 46$ a $\tau_H \le 23$ períodos en $M = [0.10, 0.28)$ sin caja negra numérica.
   - **Proposición 1 y testigo afilado en $M_0 = [0.05, 0.10)$:** corrige la condición analítica real de signo negativo en $\partial u/\partial \eta$ ($c < 1 - L = 0.25$) y afila el plazo de salida en $M_0$ hasta $\tau_{.1} \le 9$ (holgura $+0.5253$ frente a MR-Tabla 4), auditado contra el techo CEGIS $\Psi(0.10) = -35.1667$ con derivada certificada $\inf_{M_0} \Psi' \ge 91.23 > 6.4234$.
   - **Proposición 3 — síntesis 100% LP determinista (`Caso 1A` y `Caso 1C`):** elimina íntegramente PyTorch/Adam sustituyéndolo por HiGHS ralo (`57` nodos / `2.29 s` y versión podada `22` nodos / `0.95 s`), logrando **$T_\theta = 9$** y **$T_{\text{full}} = 5$**; mediante cadenas no estacionarias $\{J_k\}$ se descompone la brecha residual: **$T_{\text{ns}}(\mathcal{P}) = 5 \to T_{\text{ns}}(\theta_0) = 4 = \tau_H^{\text{VFI}}$**.
   - **Proposición 4 — cascada casi hasta Skiba (`Caso 1B`):** 16 subcajas ortogonales $(4_A \times 4_\beta)$ en 5 etapas contiguas sobre $[0.0030, 0.28)$ ($l_0 = 0.1695 > h/2 = 0.14$) certifican **$T_{\text{total}} \le 52$** (`21+13+8+5+5`, salida mínima $+0.1326$), cerrando el $99.5\%$ del rango $[0.0025, 0.10)$ de la Figura 6 de MR ($98.6\%$ del ancho $(S_A, 0.10)$).
   - **Proposición 2:** certificación analítica en intervalos `Decimal` de 50 dígitos y Wronskiano de las salidas adversas en $M$ ($l_0 = 0.44$) y $H_1 = [0.28, 0.80)$ ($l_0 = 0.60$ y $l_0 = 0.57$).

2. **Resolución analítica pura de la Nota al pie 1 y ley heurística de segundo orden (Teorema 2, Corolario 1 y Observación 1):**
   - Prueba analítica pura para todo $A$ suficientemente grande de **$S_A^{\text{fix}}(1) < S_A$** mediante cota $T_{\text{esc}}(A) \le T_M(A) = O(\log\log A)$ y ganancia $\beta^{T_M} g_{T_M} \gg O(A^{-1})$ sin recurrir a la VFI.
   - Ley asintótica heurística de segundo orden $\Delta_k = A^{1/r}S_A - (\delta/c_K)^{1/r} \asymp (\ln\ln A / (\ln A)^{1-\kappa})^{1/\mu_K}$ ($\mu_K = 0.77661$, $\kappa = 0.07512$) y sensibilidad envolvente $(S_A - S_A^{\text{fix}}(1))/S_A \asymp \Delta_k \Delta W_A^+$, verificadas por VFI $\log k$ hasta $A = 10^8$ ($L_{\text{ss}} = 7/9 \approx 0.7778$).

3. **Teoría converso-estocástica, Markov comprimido, ruina endógena y cajas anchas (`Casos 2–6`):**
   - **Teorema 3 (converso de Doob-FPBB bajo (A1)–(A3), análogo del Teorema 7 de MR):** equivalencia bajo compacidad entre escape casi seguro con tiempo esperado uniformemente acotado y existencia de super-barreras de supermartingala con brecha $\varepsilon_0 > 0$.
   - **Proposición 5 (`Caso 2`, ruina exógena $p \in [0\%, 2.0\%]$):** 60 bandas contiguas sobre $\tilde{\beta}_p \in [0.950502, 0.9701]$ con invariancia exacta a $V_{\text{ruin}}$ y plazo comprimido **$T^*_{\text{CEGIS}}(2.0\%) = 5$** (supervivencia $90.4\%$).
   - **Proposición 6 (`Caso 3`, Markov $(G, B)$ hasta $p = 12\%$):** parejas acopladas de permanencia $(B_{G,\theta}, B_{B,\theta})$ comprimen la cota esperada de escape $\mathbb{E}[\tau]$ de **$1\,480\text{–}13\,323$** a **$35.1\text{–}38.8$ períodos** ($\varepsilon_0^{\text{comp}} \ge 0.3869$, frente a $\mathbb{E}_{\text{VFI}}[\tau] \approx 5.81\text{–}5.92$), con las **1,054 hojas** continuas de $H_{1,B}$ exportadas y re-auditadas.
   - **Proposición 7 (`Caso 4`, régimen $AK$ continuo por tramos):** $T_{AK} = 4$ y $m_{H_2,[3.5,\infty),\text{iv}} = +59.7121$.
   - **Proposición 8 (`Caso 5`, ruina endógena $p(K) = p\mathbf{1}_{K<0.28}, V_{\text{ruin}}=-60$):** *huida endógena hacia la seguridad* en VFI ($\tau_{\text{VFI}}: 4 \to 3$) y certificados CEGIS-LP con $T^* = 5$.
   - **Proposición 9 (`Caso 6`, pruebas de estrés en cajas anchas):** `MR_Box_7_1` ($8$ subcajas, $29.9$ s síntesis / $10.66$ s re-verificación) y `Macro_10x_Box` ($128$ subcajas, $745.7$ s síntesis / $160.21$ s re-verificación), ambos con $T_{\text{full}} = 6$. Verificación independiente automatizada en `.github/workflows/verify.yml`.

---

## Estructura del repositorio

```text
mvs-bellman-barriers/
├── .github/workflows/verify.yml # CI público en GitHub Actions (compila Rust y audita Casos 1-6)
├── audit_standalone.py          # Verificador minimalista autocontenido (330 líneas, 0 deps externas, Lema 11 ln())
├── cegis_certificates.json.xz   # 100% de certificados exportados Casos 1-6 (incl. 1054 hojas H1_B, 5.754 MB)
├── pwl_model.py                 # Representación exacta log-PWL (cero PyTorch)
├── interval_audit.py            # Capa Decimal 50 dígitos (ln() Lema 11 sin libm) + Numba IEEE-754
├── rust_verifier/               # Núcleo nativo en Rust sin crates ni libm (iv_ln_pt Lema 11, B&B 3D/1D)
│   ├── Cargo.toml
│   ├── build.py                 # Compila mvs_verifier.dll / libmvs_verifier.so/.dylib vía rustc
│   └── src/lib.rs
├── cegis_verifier.py            # Interfaz dual Rust/Python + verificadores B&B y auditoría terminal
├── cegis_synth.py               # Motor Proposer-Verifier CEGIS-LP ralo determinista (HiGHS, Casos 1-6)
├── progress_bar.py
├── verify_article_a.py          # Reproducción y re-auditoría completa (Sec. 3-5, VFI Caso 5, JSON.xz 1-6)
├── generate_figures.py          # Genera fig1_barrier_es, fig2_scaling_es, fig3_stochastic_es (.svg/.png)
├── fig1_barrier_es.{svg,png}
├── fig2_scaling_es.{svg,png}
├── fig3_stochastic_es.{svg,png}
├── mvs_articulo_a_es.typ        # Fuente del manuscrito en Typst
├── mvs_articulo_a_es.pdf        # Manuscrito compilado en PDF
└── requirements.txt             # numpy, scipy, numba, matplotlib, typst (cero torch)
```

---

## Instalación y reproducibilidad

### 1. Dependencias Python
```bash
pip install -r requirements.txt
```

### 2. Verificación formal minimalista libre de dependencias (`audit_standalone.py`)
```bash
# Re-auditoría completa (330 líneas, stdlib únicamente, funciones ln() vía Lema 11 de MR):
python -u audit_standalone.py cegis_certificates.json.xz

# Modo 100% Python puro en aritmética Decimal de 50 dígitos (sin DLL en Rust, p. ej. Caso 4):
python -u audit_standalone.py cegis_certificates.json.xz --pure-python --case 4
```

### 3. Acelerador nativo en Rust (opcional) y suite completa
```bash
python rust_verifier/build.py
python -u verify_article_a.py --full-audit
python -u verify_article_a.py --full-audit --audit-only
python -u generate_figures.py
python -c "import typst; typst.compile('mvs_articulo_a_es.typ', output='mvs_articulo_a_es.pdf')"
python -u cegis_synth.py --all --seed 42
```

---

## Licencia
Distribuido bajo licencia MIT ([LICENSE](LICENSE)).
