# Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada bajo Rendimientos Crecientes

[![DOI](https://zenodo.org/badge/1467613115.svg)](https://doi.org/10.5281/zenodo.24464158)
[![Verify CEGIS Certificates](https://github.com/lordtiva/mvs-bellman-barriers/actions/workflows/verify.yml/badge.svg)](https://github.com/lordtiva/mvs-bellman-barriers/actions/workflows/verify.yml)

Código, formalización mecanizada en **Lean 4** (`13` módulos, `0` `sorry`), certificados formales **CEGIS-LP deterministas** auditados por aritmética de intervalos sin `libm`, figuras y manuscrito en Typst construidos como extensión independiente, auditable y autocontenida sobre *Minimum Viable Scale* de Milei y Reidel (octubre de 2026).

- **Archivo permanente en Zenodo (`v1.0.1`):** DOI [`10.5281/zenodo.24467170`](https://doi.org/10.5281/zenodo.24467170) ([registro](https://zenodo.org/records/24467170)) — Concept DOI (todas las versiones): [`10.5281/zenodo.24464158`](https://doi.org/10.5281/zenodo.24464158).

---

## Resultados principales certificados

1. **Afilamiento determinista, cadena no estacionaria y cierre casi hasta el punto de Skiba ($46 \to 23 \to 9 \to 5 \to 4$):**
   - **Teorema 1 (afilamiento del Teorema 9 de MR — barrera afín analítica cerrada de 1 paso):** reduce la holgura de bloque de 2 pasos de Milei–Reidel de $\tau_H \le 46$ a $\tau_H \le 23$ períodos en $M = [0.10, 0.28)$ sin caja negra numérica.
   - **Proposición 1 y testigo afilado en $M_0 = [0.05, 0.10)$:** corrige la condición analítica real de signo negativo en $\partial u/\partial \eta$ ($c < 1 - L = 0.25$) y afila el plazo de salida en $M_0$ hasta $\tau_{.1} \le 9$ (holgura $+0.5253$ frente a MR-Tabla 4), auditado contra el techo CEGIS $\Psi(0.10) = -35.1667$ con derivada certificada $\inf_{M_0} \Psi' \ge 91.23 > 6.4234$.
   - **Proposición 3 — síntesis 100% LP determinista (`Caso 1A` y `Caso 1C`):** sintetiza mediante HiGHS ralo (`57` nodos / `2.29 s` y versión podada `22` nodos / `0.95 s`), logrando **$T_\theta = 9$** y **$T_{\text{full}} = 5$**; mediante cadenas no estacionarias $\{J_k\}$ se descompone la brecha residual: **$T_{\text{ns}}(\mathcal{P}) = 5 \to T_{\text{ns}}(\theta_0) = 4 = \tau_H^{\text{VFI}}$**.
   - **Proposición 4 — cascada casi hasta Skiba (`Caso 1B`):** 16 subcajas ortogonales $(4_A \times 4_\beta)$ en 5 etapas contiguas sobre $[0.0030, 0.28)$ ($l_0 = 0.1695 > h/2 = 0.14$) certifican **$T_{\text{total}} \le 52$** (`21+13+8+5+5`, salida mínima $+0.1326$), cerrando el $99.5\%$ del rango $[0.0025, 0.10)$ de la Figura 6 de MR ($98.6\%$ del ancho $(S_A, 0.10)$).
   - **Proposición 2:** certificación analítica en intervalos `Decimal` de 50 dígitos y Wronskiano de las salidas adversas en $M$ ($l_0 = 0.44$) y $H_1 = [0.28, 0.80)$ ($l_0 = 0.60$ y $l_0 = 0.57$).

2. **Resolución analítica pura de la Nota al pie 1 y ley de segundo orden (Teorema 2, Corolario 1 y Observación 1):**
   - Prueba analítica pura para todo $A$ suficientemente grande de **$S_A^{\text{fix}}(1) < S_A$** mediante cota $T_{\text{esc}}(A) \le T_M(A) = O(\log\log A)$ y ganancia $\beta^{T_M} g_{T_M} \gg O(A^{-1})$ sin recurrir a la VFI.
   - **Ley asintótica de segundo orden elevada a teorema en Lean 4** ([`lean/MVS/Theorem2SecondOrder.lean`](lean/MVS/Theorem2SecondOrder.lean)): $\Delta_k = A^{1/r}S_A - (\delta/c_K)^{1/r} \asymp (\ln\ln A / (\ln A)^{1-\kappa})^{1/\mu_K}$ ($\mu_K = 0.77661$, $\kappa = 0.07512$, $\lambda_K = 1.04$, $L_{\text{ss}} = 7/9$) más la cota superior de la brecha relativa $(S_A - S_A^{\text{fix}}(1))/S_A \le \frac{8}{\eta k_*}\Delta_k \Delta W_A^+ = O((\ln\ln A)^{1+1/\mu_K} / (\ln A)^{1+(1-\kappa)/\mu_K})$ vía envolvente de Milgrom–Segal.

   - **Proposición 5 (`Caso 4`, régimen $AK$ continuo por tramos):** $T_{AK} = 4$ y $m_{H_2,[3.5,\infty),\text{iv}} = +59.7121$.
   - **Proposición 6 (`Caso 6`, pruebas de estrés en cajas anchas):** `MR_Box_7_1` ($8$ subcajas, $29.9$ s síntesis / $10.66$ s re-verificación) y `Macro_10x_Box` ($128$ subcajas, $745.7$ s síntesis / $160.21$ s re-verificación), ambos con $T_{\text{full}} = 6$. Verificación independiente automatizada en `.github/workflows/verify.yml`.

3. **Teoría converso-estocástica, Markov comprimido y ruina endógena (`Casos 2, 3 y 5`):**
   - **Teorema 3 (converso de Doob-FPBB bajo (A1)–(A3)):** equivalencia bajo compacidad entre escape casi seguro con tiempo esperado uniformemente acotado y existencia de super-barreras de supermartingala con brecha $\varepsilon_0 > 0$, acopladas directamente a la selección endógena de políticas óptimas.
   - **Proposición 7 (`Caso 2`, ruina exógena $p \in [0\%, 2.0\%]$):** 60 bandas contiguas sobre $\tilde{\beta}_p \in [0.950502, 0.9701]$ con invariancia exacta a $V_{\text{ruin}}$ y plazo comprimido **$T^*_{\text{CEGIS}}(2.0\%) = 5$** (supervivencia $90.4\%$).
   - **Proposición 8 (`Caso 3`, Markov $(G, B)$ hasta $p = 12\%$):** parejas acopladas de permanencia $(B_{G,\theta}, B_{B,\theta})$ comprimen la cota esperada de escape $\mathbb{E}[\tau]$ de **$1\,480\text{–}13\,323$** a **$35.1\text{–}38.8$ períodos** ($\varepsilon_0^{\text{comp}} \ge 0.3869$, frente a $\mathbb{E}_{\text{VFI}}[\tau] \approx 5.81\text{–}5.92$), con las **1,054 hojas** continuas de $H_{1,B}$ exportadas y re-auditadas.
   - **Proposición 9 (`Caso 5`, ruina endógena $p(K) = p\mathbf{1}_{K<0.28}, V_{\text{ruin}}=-60$):** *huida endógena hacia la seguridad* en VFI ($\tau_{\text{VFI}}: 4 \to 3$) y certificados CEGIS-LP con $T^* = 5$.

4. **Formalización mecanizada en Lean 4 ([`lean/`](lean/README.md)):**
   - **13 módulos en Lean 4 (`v4.36.0` + Mathlib4)** con **0 `sorry`** y **0 axiomas extra** (únicamente `[propext, Classical.choice, Quot.sound]`): Lema 11 (`Lemma11`), Lema 12 global en todo $(0,\infty)$ certificado con 131 segmentos racionales (`Lemma12` + `Lemma12Cert`), Lema 1 y Teorema 1 (`Theorem1`), Proposición 1 (`Proposition1`), Proposición 2 + Tabla 2 (`Proposition2` + `Proposition2Cert`), Teorema 2 + Corolario 1 + Teorema de segundo orden (`Theorem2` + `Theorem2SecondOrder`), Lema 2 + Corolario 2 + Teorema 3 (`Stochastic`), solidez CEGIS-PWL + certificación en kernel de $B_\theta$ de 22 nodos (`CEGIS` + `CEGISCert`), y teoría estructural completa de las Proposiciones 3–9 (`Section5Theory`).

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
├── lean/                        # Formalización mecanizada en Lean 4 (v4.36.0 + Mathlib4, 0 sorry, 0 axiomas extra)
│   ├── README.md                # Mapa completo de los 13 módulos y comandos de auditoría de axiomas
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── MVS.lean                 # Punto de entrada del proyecto Lean 4
│   └── MVS/                     # Lemma11, Lemma12(+Cert), Theorem1, Prop1-2(+Cert), Theorem2(+SecondOrder), Stochastic, CEGIS(+Cert), Section5Theory
├── cegis_verifier.py            # Interfaz dual Rust/Python + verificadores B&B y auditoría terminal
├── cegis_synth.py               # Motor Proposer-Verifier CEGIS-LP ralo determinista (HiGHS, Casos 1-6)
├── progress_bar.py
├── verify_all.py                # Reproducción y re-auditoría completa (Sec. 3-6, VFI Caso 5, JSON.xz 1-6)
├── generate_figures.py          # Genera las 7 figuras del manuscrito (.svg/.png)
├── fig1_barrier_es.{svg,png}
├── fig2_scaling_es.{svg,png}
├── fig3_stochastic_es.{svg,png}
├── fig_arch_es.{svg,png}
├── fig_nearskiba_es.{svg,png}
├── fig_markov_es.{svg,png}
├── fig_endo_policy_es.{svg,png}
├── mvs_bellman_barriers_es.typ  # Fuente del manuscrito en Typst
├── mvs_bellman_barriers_es.pdf  # Manuscrito compilado en PDF
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
python -u verify_all.py --full-audit
python -u verify_all.py --full-audit --audit-only
python -u generate_figures.py
python -c "import typst; typst.compile('mvs_bellman_barriers_es.typ', output='mvs_bellman_barriers_es.pdf')"
python -u cegis_synth.py --all --seed 42
```

### 4. Verificación mecanizada en Lean 4 (`lean/`)
```bash
cd lean
lake exe cache get
lake build
```
Ver [`lean/README.md`](lean/README.md) para el mapa detallado de los 13 módulos y el script de auditoría `#print axioms`.

---

## Cita sugerida (Zenodo)
```bibtex
@software{segura_2026_mvs_bellman_barriers,
  author       = {Segura, Marcelo},
  title        = {Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada bajo Rendimientos Crecientes},
  year         = 2026,
  publisher    = {Zenodo},
  version      = {v1.0.1},
  doi          = {10.5281/zenodo.24467170},
  url          = {https://doi.org/10.5281/zenodo.24467170}
}
```

## Licencia
Distribuido bajo licencia MIT ([LICENSE](LICENSE)).
