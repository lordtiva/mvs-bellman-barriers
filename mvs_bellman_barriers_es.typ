#set page(
  paper: "a4",
  margin: (top: 2.3cm, bottom: 2.3cm, left: 2.4cm, right: 2.4cm),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 8.5pt, fill: luma(110), style: "italic")
      #grid(
        columns: (3fr, 1fr),
        align: (left, right),
        [Barreras de Bellman Afiladas y Supervivencia Estocástica],
        [M. Segura (2026)]
      )
      #line(length: 100%, stroke: 0.4pt + luma(180))
    ]
  },
)

#set text(font: "New Computer Modern", size: 10.5pt, lang: "es")
#set par(justify: true, leading: 0.62em, first-line-indent: 0pt)
#set figure(numbering: none)
#show figure.caption: it => {
  set text(size: 9pt, fill: luma(55))
  it.body
}
#set heading(numbering: "1.1.")
#show heading: it => {
  set text(fill: rgb("#0b2c4d"), weight: "bold")
  v(0.7em)
  it
  v(0.35em)
}

#let thm_box(kind, num, title, body) = {
  block(
    width: 100%,
    inset: (x: 10pt, y: 8pt),
    radius: 3pt,
    fill: rgb("#f4f7fb"),
    stroke: (left: 2.5pt + rgb("#1f4e78"), rest: 0.4pt + rgb("#d0dce8")),
    [
      #text(weight: "bold", fill: rgb("#0b2c4d"))[#kind #num]
      #if title != "" and title != [] [ #text(style: "italic", fill: rgb("#1f4e78"))[(#title).] ] else [.]
      #h(4pt)
      #body
    ],
  )
}

#let obs_box(num, title, body) = {
  block(
    width: 100%,
    inset: (x: 10pt, y: 8pt),
    radius: 3pt,
    fill: rgb("#fcfaf5"),
    stroke: (left: (paint: rgb("#b45309"), thickness: 2.2pt, dash: "dashed"), rest: 0.4pt + rgb("#e6dcc8")),
    [
      #text(weight: "bold", fill: rgb("#92400e"))[Observación #num]
      #if title != "" and title != [] [ #text(style: "italic", fill: rgb("#b45309"))[(#title).] ] else [.]
      #h(4pt)
      #body
    ],
  )
}

#let cert_box(title: "Certificación y Desigualdades Verificadas", body) = {
  block(
    width: 100%,
    inset: (left: 8pt, right: 6pt, y: 5pt),
    radius: 2pt,
    fill: rgb("#f8fafc"),
    stroke: (left: 1.5pt + rgb("#1b7837")),
    [
      #text(style: "italic", weight: "bold", fill: rgb("#14532d"))[#title.] #h(4pt) #body
    ],
  )
}

#let alg_box(num, title, body) = {
  block(
    width: 100%,
    inset: (x: 10pt, y: 8pt),
    radius: 3pt,
    fill: rgb("#f9fafb"),
    stroke: (top: 1.4pt + rgb("#0b2c4d"), bottom: 1.4pt + rgb("#0b2c4d"), rest: 0.4pt + luma(200)),
    [
      #text(weight: "bold", fill: rgb("#0b2c4d"))[Algoritmo #num:] #text(style: "italic", fill: rgb("#1f4e78"))[#title]
      #v(0.25em)
      #line(length: 100%, stroke: 0.4pt + luma(200))
      #v(0.25em)
      #body
    ],
  )
}

#let proof_block(title: "Demostración", body) = {
  block(
    width: 100%,
    inset: (left: 8pt, right: 4pt, y: 4pt),
    stroke: (left: 1.2pt + luma(180)),
    [
      #text(style: "italic", weight: "bold", fill: luma(70))[#title.] #h(4pt) #body #h(1fr) $square.stroked$
    ],
  )
}

// ============================================================================
// PORTADA / TÍTULO Y RESUMEN
// ============================================================================
#align(center)[
  #text(size: 16.5pt, weight: "bold", fill: rgb("#0b2c4d"))[
    Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada \
    bajo Rendimientos Crecientes
  ]
  #v(0.45em)
  #text(size: 11pt, style: "italic", fill: rgb("#1f4e78"))[
    Síntesis Adaptativa CEGIS-LP, Análisis Asintótico CES y Certificados de Intervalos sobre _Minimum Viable Scale_
  ]
  #v(0.8em)
  #text(size: 11pt, weight: "bold")[Marcelo Segura]
  #v(0.2em)
  #text(size: 9.5pt, fill: luma(90))[Manuscrito Técnico — Versión Autónoma Reproducible]
  #v(0.2em)
  #text(size: 9pt, fill: luma(110))[Noviembre de 2026 #h(6pt) · #h(6pt) #link("https://doi.org/10.5281/zenodo.24464158")[DOI: `10.5281/zenodo.24464158`]]
]

#v(0.8em)
#block(
  width: 100%,
  inset: 11pt,
  radius: 4pt,
  fill: rgb("#f9fafb"),
  stroke: 0.5pt + luma(200),
  [
    #text(weight: "bold", fill: rgb("#0b2c4d"))[Resumen.]
    Presentamos una metodología general para certificar barreras de Bellman de primer paso en programación dinámica no convexa con puntos de Skiba, combinando análisis asintótico de segundo orden cerrado, síntesis determinista por programación lineal dispersa guiada por contraejemplos (_CEGIS-LP / log-PWL_) sin entrenamiento neuronal, un teorema converso estocástico de Doob acoplado a selección óptima y auditoría continua por intervalos libre de `libm`. Evaluamos y desplegamos todo el marco sobre la economía canónica con rendimientos crecientes _Minimum Viable Scale_ (MVS) de Milei y Reidel (2026) como banco de pruebas de referencia. El artículo articula cuatro aportes principales: (i) *Afilamiento determinista y escalabilidad:* reducimos a la mitad la cota analítica de permanencia (de $tau_H <= 46$ a $tau_H <= 23$), comprimimos el plazo certificado en $M = [0.10, 0.28)$ hasta $T_"full" = 5$ ($T_"ns" (theta_0) = 4 = tau_H^"VFI"$), cerramos el $99.5\%$ de la brecha hasta el umbral de Skiba mediante una cascada continua desde $b_"ext" = 0.0030$ ($T_"total" <= 52$) y demostramos transferibilidad al régimen híbrido CES--AK y a cajas paramétricas $10 times$ anchas; (ii) *Asintótica pura ($A -> oo$):* demostramos analíticamente sin VFI que $T_"esc" (A) = O(log log A)$ y $S_A^"fix" (1) < S_A$ para todo $A$ grande bajo $beta theta > 1$, acompañados por una ley de segundo orden que explica la persistencia del $+3.9\%$ en $A = 10^8$; (iii) *Teoría converso-estocástica y dicotomía VFI:* demostramos un teorema converso de Doob acoplado directamente a la selección endógena de políticas óptimas, revelamos en VFI el contraste entre colapso de inversión bajo ruina exógena y *huida hacia la seguridad* bajo recesión Markoviana o ruina endógena $p(K) = p bold(1)_(K < 0.28)$, y comprimimos las cotas de Markov hasta $p = 12\%$ en más de dos órdenes de magnitud ($E[tau] <= 35.1"–"38.8$); y (iv) *Verificación formal integral:* toda la arquitectura matemática queda mecanizada en *Lean 4* (`13` módulos, `0` `sorry`, cero axiomas adicionales) y respaldada por certificados re-auditables de manera autónoma.

    #v(0.3em)
    #text(weight: "bold", fill: rgb("#0b2c4d"))[Palabras clave:] Programación dinámica no convexa, puntos de Skiba, barreras de Bellman, CEGIS-LP, aritmética de intervalos, parada opcional de Doob, equivalencia asintótica CES, Lean 4.
  ],
)

// ============================================================================
// SECCIÓN 1: INTRODUCCIÓN Y MAPA EPISTEMOLÓGICO
// ============================================================================
= Introducción y Mapa Epistemológico

Los modelos de desarrollo e industrialización con rendimientos crecientes a escala exhiben trampas de pobreza y umbrales críticos de capital conocidos como puntos de Skiba o Dechert--Nishimura (Skiba, 1978; Dechert y Nishimura, 1983). En la monografía _Minimum Viable Scale: Bellman Barriers and the Economics of Survival_, Milei y Reidel (2026) —en adelante MR— sustituyen el cálculo heurístico en malla fija por el marco de _Barreras de Bellman de Primer Paso_ (_First Passage Bellman Barriers_, FPBB): mediante barreras analíticas acotan la función valor óptima $V(K)$ desde abajo por testigos factibles $W(K)$ y desde arriba por techos de Bellman $Psi(K)$, extrayendo garantías rigurosas en tiempo finito sobre el plazo de escape desde la región de tránsito $M = [0.10, 0.28)$ hacia el umbral productivo $h = 0.28$ y sobre la extinción por debajo de la escala mínima viable $b = 0.10$.

Este artículo desarrolla una metodología general e independiente para toda la clase de problemas de programación dinámica no convexa con puntos de Skiba —combinando síntesis adaptativa determinista _CEGIS-LP_, un teorema converso estocástico de Doob acoplado a selección óptima, análisis asintótico de segundo orden y verificación formal en Lean 4— y emplea el modelo MVS como banco de pruebas canónico. Más allá de refinar las cotas del modelo base, el trabajo aporta cuatro contribuciones estructurales:

1. *Afilamiento determinista, cascada hasta $b_"ext" = 0.0030$ y arquitectura CEGIS-LP escalable:* Demostramos en la Sección 3 que la cota original $tau_H <= 46$ de MR sufre una pérdida artificial por el bloqueo algebraico de dos pasos. Una barrera afín de un paso $B_1 (K)$ reduce exactamente a la mitad el plazo máximo ($tau_H <= 23$, *Teorema 1*), el análisis en $M_0 = [0.05, 0.10)$ fija la condición exacta $c < 1 - L = 0.25$ y certifica $tau_(.1) <= 9$ (*Proposición 1*), y el Wronskiano cierra continuamente las salidas adversas (*Proposición 2*). En la Sección 5, la arquitectura desacoplada _Proposer--Verifier_ sintetiza tripletas continuas `log-PWL` $(B_theta, Psi, W)$ alcanzando $T_theta = 9$ y $T_"full" = 5$, descompone con cadenas no estacionarias la brecha frente al óptimo de malla ($T_"ns" (cal(P)) = 5 -> T_"ns" (theta_0) = 4 = tau_H^"VFI"$, *Proposición 3*), cierra el $99.5\%$ de la brecha $[0.0025, 0.10)$ hasta el umbral de Skiba mediante una cascada de $5$ etapas desde $b_"ext" = 0.0030$ ($T_"total" <= 52$, *Proposición 4*), y demuestra transferibilidad al régimen híbrido CES--AK (*Proposición 5*) y a cajas paramétricas $10 times$ anchas (*Proposición 6*).

2. *Resolución analítica pura de $S_A^"fix" (1) < S_A$ ($A -> oo$) y ley cuantitativa de segundo orden:* En la Sección 4 resolvemos la cuestión abierta sobre trabajo elástico frente a trabajo fijo cuando la productividad total de los factores $A -> oo$. El *Teorema 2* (Parte 1) prueba la convergencia uniforme hacia el límite común $(delta\/c_K)^(1\/r) = 0.000800$, el *Corolario 1* extiende la unicidad al régimen de paciencia débil $beta theta > 1$ vía envolvente de Milgrom--Segal, y la Parte 2 eleva la desigualdad finita $S_A^"fix" (1) < S_A$ a teorema analítico puro para todo $A$ grande mediante $T_"esc" (A) <= T_M (A) = O(log log A)$. Además, la *Observación 1* (y su esquema de prueba en el Apéndice A.5) formula la ley exacta de segundo orden $Delta_k (A) asymp ([log log A]\/[(log A)^(1-kappa)])^(1\/mu_K)$ —mecanizada en Lean 4 junto con la cota superior de la brecha relativa—, explicando cuantitativamente por qué incluso en $A = 10^8$ persiste un desvío del $+3.9\%$ respecto del límite asintótico y por qué la razón envolvente decae suavemente de $29.35$ a $22.36$ (Tabla 3).

3. *Teorema converso estocástico de Doob acoplado a selección óptima y dicotomía económica VFI:* En la Sección 6 demostramos el *Teorema 3*, análogo estocástico del teorema de completitud de MR: bajo compacidad, el escape casi seguro en tiempo medio uniformemente acotado equivale a la existencia de súper-barreras de supermartingala con brecha estricta $epsilon.alt_0 > 0$. A diferencia de los teoremas conversos clásicos de Foster--Lyapunov (Kushner, 1967; Meyn y Tweedie, 2009) y de los certificados estocásticos para sistemas cerrados bajo dinámica fija (Prajna et al., 2007), nuestro resultado acopla la supermartingala directamente a la *selección endógena de políticas óptimas* mediante $inf (V - V_M^"stay") > 0$, certificando toda política estacionaria óptima $pi^*$ sin conocerla explícitamente. Computacionalmente, la VFI estocástica continua revela una nítida *dicotomía económica* (Tabla 6): bajo ruina exógena el ahorro colapsa y el umbral de Skiba casi se triplica, mientras que bajo recesión recuperable de Markov o ruina endógena $p(K) = p bold(1)_(K < 0.28)$ el planificador ejecuta una *huida precautoria hacia la seguridad* (elevando inversión y trabajo; en ruina endógena $tau_"VFI"$ cae de $4$ a $3$). Mediante CEGIS-LP certificamos $60$ bandas continuas de ruina exógena con invariancia exacta a $V_"ruin"$ (*Proposición 7*), parejas acopladas de Markov $(B_(G,theta), B_(B,theta))$ que comprimen $E[tau]$ hasta $35.1"–"38.8$ períodos frente al óptimo VFI $approx 5.81"–"5.92$ (*Proposición 8*), y el régimen de ruina endógena (*Proposición 9*).

4. *Formalización integral en Lean 4 y auditoría terminal libre de `libm`:* Lejos de limitarnos a scripts numéricos ad hoc, toda la arquitectura matemática del manuscrito se encuentra mecanizada en **Lean 4** (`v4.36.0` + Mathlib4, `13` módulos, `0` `sorry`, cero axiomas adicionales más allá de `[propext, Classical.choice, Quot.sound]`), mientras que las tablas masivas de certificados en `cegis_certificates.json.xz` se re-auditan con un verificador minimalista independiente (`audit_standalone.py`, cero dependencias externas) y logaritmos sin `libm` en Rust/`Decimal` (Sección 7).

#v(0.4em)
#figure(
  table(
    columns: (1.5fr, 1.35fr, 1.85fr, 1.7fr),
    inset: 5.5pt,
    align: left,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.6pt)[Resultado (Sección)],
      text(fill: white, weight: "bold", size: 8.6pt)[Objeto / Dominio],
      text(fill: white, weight: "bold", size: 8.6pt)[Cota o Propiedad Probada],
      text(fill: white, weight: "bold", size: 8.6pt)[Método de Prueba],
    ),
    [#text(size: 8.4pt)[*Lema 1 & Teorema 1* (3.2)]], [#text(size: 8.4pt)[Barrera afín $B_1 (K)$ en $M$]], [#text(size: 8.4pt)[$B_1 >= -43.356$; $tau_H <= 23$]], [#text(size: 8.4pt)[Analítico cerrado + Lean 4]],
    [#text(size: 8.4pt)[*Proposición 1* (3.3)]], [#text(size: 8.4pt)[Testigo afilado en $M_0$]], [#text(size: 8.4pt)[$c < 0.25$; $tau_(.1) <= 9$ ($+0.5253$)]], [#text(size: 8.4pt)[Analítico + techo LP $Psi' >= 91.23$]],
    [#text(size: 8.4pt)[*Proposición 2* (3.4)]], [#text(size: 8.4pt)[Salidas $E^+(K, a; l_0)$ en $M, H_1$]], [#text(size: 8.4pt)[$Delta'' < 0$; $Q <= -0.04375$]], [#text(size: 8.4pt)[Wronskiano + `Decimal` 50 díg.]],
    [#text(size: 8.4pt)[*Teo. 2, Cor. 1, Obs. 1* (4)]], [#text(size: 8.4pt)[Escalado $A -> oo$, $beta theta > 1$]], [#text(size: 8.4pt)[$S_A^"fix" (1) < S_A$; $T_"esc" = O(log log A)$]], [#text(size: 8.4pt)[Asintótica pura + Lean 4 + VFI]],
    [#text(size: 8.4pt)[*Prop. 3* (Caso 1A/1C, 5.2)]], [#text(size: 8.4pt)[LP determinista + cadena $\{J_k\}$]], [#text(size: 8.4pt)[$T_theta = 9$; $T_"full" = 5$; $T_"ns" = 5\/4$]], [#text(size: 8.4pt)[HiGHS-LP + B&B 3D + Lean 4]],
    [#text(size: 8.4pt)[*Prop. 4* (Caso 1B, 5.2)]], [#text(size: 8.4pt)[Cascada $[0.003, 0.28)$ ($16$ cajas)]], [#text(size: 8.4pt)[$T_"total" <= 52$; salida $>= +0.1326$]], [#text(size: 8.4pt)[5 etapas contiguas LP + Lema 11 de MR]],
    [#text(size: 8.4pt)[*Prop. 5* (Caso 4 AK, 5.3)]], [#text(size: 8.4pt)[Régimen híbrido CES--AK]], [#text(size: 8.4pt)[$Psi_"AK" (0.28) = +243.46$; $T_"AK" = 4$]], [#text(size: 8.4pt)[CEGIS-LP + rayo homogéneo 50 díg.]],
    [#text(size: 8.4pt)[*Prop. 6* (Caso 6, 5.3)]], [#text(size: 8.4pt)[Cajas anchas $10 times$ ($8 + 128$ bx)]], [#text(size: 8.4pt)[$T_"full" = 6$; $M >= +0.5569$]], [#text(size: 8.4pt)[LP particionado + auditoría B&B]],
    [#text(size: 8.4pt)[*Teorema 3* (Converso, 6.1)]], [#text(size: 8.4pt)[FPBB estocástica de Doob]], [#text(size: 8.4pt)[Escape c.s. + $sup E[tau] < oo <==>$ FPBB]], [#text(size: 8.4pt)[Teoría estocástica + Lean 4]],
    [#text(size: 8.4pt)[*Lema 2, Cor. 2, Prop. 7* (Caso 2, 6.1/6.3)]], [#text(size: 8.4pt)[Ruina exóg. $p in [0, 2\%]$ ($60$ b.)]], [#text(size: 8.4pt)[Invariante $V_"ruin"$; $T^*_"CEGIS" = 5$]], [#text(size: 8.4pt)[Doob + CEGIS-LP + interv. sin `libm`]],
    [#text(size: 8.4pt)[*Prop. 8* (Caso 3, 6.3)]], [#text(size: 8.4pt)[Markov $(G, B)$ hasta $p = 12\%$]], [#text(size: 8.4pt)[$E[tau] <= 35.1"–"38.8$; $1 thin 054$ hojas $H_(1,B)$]], [#text(size: 8.4pt)[$(B_(G,theta), B_(B,theta))$ acopladas + B&B 3D]],
    [#text(size: 8.4pt)[*Prop. 9* (Caso 5, 6.3)]], [#text(size: 8.4pt)[Ruina endógena $p(K) = p bold(1)_(K<0.28)$]], [#text(size: 8.4pt)[Huida endógena; $T^* = 5$; surv. $>= 90.39\%$ ($p=2\%$)]], [#text(size: 8.4pt)[VFI comparativa + CEGIS-LP]],
  ),
  caption: [Tabla 1: Mapa epistemológico de los resultados según sección, dominio y método de certificación.],
)

El resto del manuscrito sigue esta estructura: la Sección 2 sitúa el trabajo en la literatura; la Sección 3 establece las cotas analíticas cerradas y el Wronskiano continuo; la Sección 4 demuestra la equivalencia asintótica $A -> oo$ y la ley de segundo orden; la Sección 5 formaliza la arquitectura CEGIS-LP junto con la certificación, transferibilidad y escalabilidad determinista (Casos 1, 4 y 6); la Sección 6 desarrolla la teoría converso-estocástica de Doob, la dicotomía VFI y los Casos 2, 3 y 5; la Sección 7 detalla la formalización en Lean 4, la reproducibilidad y las limitaciones del método; y la Sección 8 sintetiza las conclusiones.

// ============================================================================
// SECCIÓN 2: LITERATURA RELACIONADA
// ============================================================================
= Literatura Relacionada

== Puntos de Skiba, Trampas de Pobreza y Dinámica No Convexa

Desde los trabajos seminales de Skiba (1978), Majumdar y Mitra (1982) y Dechert y Nishimura (1983), la existencia de funciones de producción localmente convexas o con costos fijos de adopción origina funciones valor no cóncavas, políticas óptimas discontinuas y un conjunto crítico de indiferencia (punto de Skiba) que separa cuencas de atracción hacia la extinción o hacia un estado estacionario próspero. Kamihigashi y Roy (2007), Akao, Kamihigashi y Nishimura (2011) y Akao, Ishii, Kamihigashi y Nishimura (2022) caracterizaron la existencia, continuidad y monotonía del capital crítico en entornos no cóncavos y no suaves; Wagener (2003) clasificó las bifurcaciones heteroclinas y globales del umbral de indiferencia en modelos dinámicos con puntos de inflexión; y Kraay y McKenzie (2014) contrastaron las predicciones empíricas de trampas de pobreza frente a dinámicas lentas de convergencia. A diferencia de estos estudios orientados a existencia o estática comparativa local, Milei y Reidel (2026) proponen certificar cotas globales de tiempo finito sobre las regiones $M_0$, $M$ y $H$ dentro de cajas compactas de incertidumbre paramétrica. Nuestro artículo afila analíticamente esas cotas y demuestra sus propiedades asintóticas y estocásticas rigurosas.

== Tecnologías CES y Trabajo Endógeno en Crecimiento

La sensibilidad de los umbrales de trampa respecto a la elasticidad de sustitución capital--trabajo ($sigma = 1\/(1 - rho) > 1$ o complementariedad bruta $rho < 0$, con $rho = -1$, $sigma = 1\/2$ en la parametrización CES armónica de referencia) y la oferta laboral elástica cuenta con una vasta tradición en macroeconomía (Acemoglu, 2009). La literatura clásica suele fijar el insumo laboral $L = overline(L)$ para preservar tratabilidad analítica en las regiones asintóticas de baja escala. Una cuestión abierta fundamental consiste en determinar en qué medida permitir la elección endógena del trabajo altera los umbrales de trampa cuando la productividad total de los factores $A$ crece sin cota. En la Sección 4 demostramos cómo el teorema asintótico $A -> oo$ colapsa la ventaja intramarginal del trabajo elástico a ritmo polilogarítmico mientras preserva el ordenamiento estricto para todo $A$ finito.

== Barreras de Bellman, Dualidad LP, Parada de Doob y Síntesis Certificada CEGIS

El respaldo formal de las barreras regionales descansa sobre tres pilares matemáticos clásicos: las desigualdades de variación y teoremas de envolvente sin diferenciabilidad bilateral de Milgrom y Segal (2002) (fundamentales para cerrar el régimen $beta theta > 1$), la teoría de viabilidad y funciones barrera/Lyapunov en sistemas discretos (Aubin, 1991), y la formulación dual mediante programación lineal continua de funciones sub-solución de Bellman (Hernández-Lerma y Lasserre, 1996). Para extender estas garantías deterministas al entorno con riesgo de ruina o transiciones de Markov utilizamos el teorema de parada opcional de Doob para supermartingalas detenidas (Doob, 1953; Williams, 1991).

En el plano algorítmico, nuestro motor se inscribe dentro de la literatura moderna de *síntesis certificada de funciones de Lyapunov y barrera mediante _CEGIS_ (_Counterexample-Guided Inductive Synthesis_)* bajo arquitectura desacoplada _Proposer--Verifier_ (Solar-Lezama, 2008; Ravanbakhsh y Sankaranarayanan, 2019; Abate et al., 2021). A diferencia de los enfoques de control neuronal (_neural Lyapunov_) que dependen de optimización no convexa o muestreo probabilístico, empleamos aquí un _Proposer_ basado en programación lineal dispersa (HiGHS; Huangfu y Hall, 2018) con inserción adaptativa de nodos en los peores contraejemplos sobre splines continuos por tramos en escala logarítmica (_log-PWL_), mientras que el $100\%$ de la validez matemática descansa sobre un _Verifier_ determinista Branch-and-Bound 3D y 1D en espacio continuo cerrado con auditoría terminal de aritmética de intervalos de redondeo dirigido (Moore et al., 2009; Tucker, 2011). Esta separación vuelve inocua la complejidad de búsqueda del _Proposer_: una barrera sintética es un certificado puro y autocontenido cuya corrección puede re-auditarse en segundos.

// ============================================================================
// SECCIÓN 3: AFILAMIENTO ANALÍTICO DETERMINISTA
// ============================================================================
= Barreras Afines de Un Paso y Afilamiento Analítico Determinista

== Marco Paramétrico y Preliminares Autocontenidos

Adoptamos como modelo canónico la especificación MVS de MR (2026): producción CES $F_A (K, L) = A [w K^rho + (1 - w) L^rho]^(theta\/rho)$ con peso simétrico $w = 1\/2$, retornos crecientes $theta = 3\/2$ y complementariedad bruta $rho = -1$ ($sigma = 1\/2$), lo que admite la forma cerrada armónica $F_A (K, L) = A (2 K L \/ (K + L))^(3\/2)$; depreciación $delta = 0.08$ ($q = 1 - delta = 0.92$); y utilidad instantánea $u(c, L) = eta log c + (1 - eta) log(1 - L)$. La caja compacta de referencia de parámetros es:
$ cal(P) = [A_-, A_+] times [q_-, q_+] times [beta_-, beta_+] times [eta_-, eta_+] = [0.749, 0.751] times [0.9199, 0.9201] times [0.9699, 0.9701] times [0.6999, 0.7001]. $
Para la región de tránsito $M = [b, h) = [0.10, 0.28)$ con umbral productivo $h = 0.28$, definimos el consumo máximo instantáneo de permanencia en $M$, $C_"max"^+ = q_+ h + F_(A_+) (h, 1) - b = 0.37495167$, y la cota superior de utilidad en $M$, $hat(R) = -0.996$. La función valor óptima $V(K)$ satisface para todo $(K, theta_"par") in M times cal(P)$ y todo par factible $(K', L) in M times [0, 1)$ la desigualdad de permanencia $V(K) >= u(q K + F_A (K, L) - K', L) + beta V(K')$.

Con el fin de garantizar la autonomía completa del documento, fijamos explícitamente cuatro objetos estructurales que intervienen en las demostraciones de las Secciones 3 y 4:
1. *Umbral físico de reposición $kappa_A$:* para cada $A > 0$, $kappa_A > 0$ es la única raíz positiva de la ecuación de mantenimiento neto $F_A (K, 1) = delta K$ (en la parametrización armónica con $A = 0.75$, $kappa_(0.75) approx 0.001425$, límite físico por debajo del cual todo capital se contrae incluso con trabajo pleno $L = 1$ y consumo nulo).
2. *Testigo factible de referencia $W_M (K)$:* en $M = [0.10, 0.28)$, la política fija $(K'_M, L_M) = (0.135, 0.68)$ con consumo peor-caso $c_M (K) = q_- K + F_(A_-) (K, 0.68) - 0.135 > 0$ y valor de continuación $-33.103$ induce el piso analítico:
   $ W_M (K) := min_(eta in {eta_-, eta_+}) { eta log c_M (K) + (1 - eta) log(1 - 0.68) } + beta_+ (-33.103), $
   alcanzando en el borde izquierdo $W_M (0.10) = -35.579855 > -35.58$.
3. *Techo analítico de Bellman $Psi^sharp (x)$:* sobre $(0, oo)$, la súper-solución analítica cerrada con desplazamiento de MR (2026) toma la forma:
   $ Psi^sharp (x) = 0.4 x - 5 x^(-1\/2) - 18.5 - 10 / 301, $
   verificando en el umbral de salida $Psi^sharp (0.28) < -27.83$ (y $Psi(0.28) < -27.83 - 10\/301$ para la versión sin desplazamiento, estando certificada globalmente en los $131$ segmentos racionales del módulo Lean 4 `MVS/Lemma12Cert.lean`).
4. *Objetos variacionales auxiliares (para el Corolario 1 en la Sección 4):* en el modelo canónico, la cota tecnológica $F_A (K, 1) < A (1 - w)^(theta\/rho)$ confina toda trayectoria factible desde $K_0 > 0$ a un compacto $[0, K_"max" (K_0, A)]$, asegurando existencia de óptimos y continuidad de $V_A (K)$. Denotamos por $u_"red" (K, s) := max_(L in [0, 1)) u(q K + F_A (K, L) - s, L)$ la utilidad reducida de transición $K -> s$, por $r_("red", K s) := partial^2 u_"red" \/ (partial K partial s)$ su derivada cruzada (estrictamente positiva en la región de supermodularidad local), y por $G_A (K)$ la correspondencia compacta de sucesores óptimos.

En su cota original de dos pasos sobre $M$, MR imponían una barrera constante por bloques $B_0 = hat(R)\/(1 - beta_-) - Delta_2\/(1 - beta_-^2) = -38.144176$ con $Delta_2 = 0.2997$, dejando un margen de apenas $2.564$ frente a $W_M (0.10)$ y exigiendo $T = 46$ períodos de permanencia para contradecir el techo $Psi^sharp (0.28)$.

== Lema 1, Teorema 1 y Reducción Analítica a la Mitad ($46 -> 23$)

Demostramos que una simple función afín con pendiente analítica exacta $m_omega$ aprovecha paso a paso todo el gradiente mínimo disponible en $M$ sin requerir búsqueda numérica.

#thm_box("Lema", "1", [Cota inferior afín de la ganancia de permanencia en $M$])[
  Sea $m_omega = (eta_- q_-) \/ C_"max"^+ = 1.717123$. Para todo $K in M = [0.10, 0.28)$, todo $theta_"par" in cal(P)$ y toda política de permanencia factible $(K', L) in M times [0, 1)$ con consumo $c = q K + F_A (K, L) - K' > 0$:
  1. Acotando el consumo respecto de $C_"max"^+ = q_+ h + F_(A_+) (h, 1) - b = 0.37495167$ por $c <= (q_+ h + F_(A_+) (h, L) - b) - q_- (h - K) - (K' - b)$ y usando la concavidad de $eta log c$ sobre $(0, C_"max"^+]$, el retorno instantáneo satisface $u(c, L) <= hat(R) - m_omega (h - K) - (eta_- \/ C_"max"^+) (K' - b)$. En consecuencia, la función afín dependiente del estado $B_1 (K) = B_* - m_omega (h - K)$ con $B_* = (hat(R) - Delta_2) \/ (1 - beta)$ satisface la desigualdad de Bellman de un paso $u(c, L) + beta B_1 (K') <= B_1 (K)$ en todo $M times M$.
  2. La holgura por distancia al borde superior $h$ respecto del máximo global $hat(R) = -0.996$ satisface la cota exacta $Delta_2^"exact" = eta_- beta_- q_- (h - b) \/ C_"max"^+ = 0.2997787 > Delta_2 = 0.2997$, alcanzando uniformemente en $cal(P)$:
     $ B_1 (K) <= B_* = -43.0465116, #h(12pt) B_1 (b) <= -43.355594, $
     con margen estado a estado $W_M (K) - B_1 (K) >= W_M (b) - B_1 (b) > 7.775594$ (y uniforme $W_M (K) - B_* > 7.4665$).
]

#proof_block(title: "Demostración del Lema 1")[
  Para cualquier transición $(K, K') in M times M$, sea $L in [0, 1)$ el esfuerzo laboral con consumo $c_0 = q K + F_A (K, L) - K' > 0$, y sea $c_1 = q_+ h + F_(A_+) (h, L) - b <= C_"max"^+$. Como el trío $(h, b, L)$ es factible en $(h, b)$ con $u(c_1, L) <= hat(R)$ y el término de ocio $(1 - eta) log(1 - L)$ se cancela idénticamente entre ambas evaluaciones, la concavidad del logaritmo ($log(c_1 \/ c_0) >= (c_1 - c_0) \/ c_1$) junto con $F_(A_+) (h, L) >= F_A (K, L)$ implican:
  $ hat(R) - u(c_0, L) >= u(c_1, L) - u(c_0, L) = eta log(c_1 \/ c_0) >= eta (c_1 - c_0) / c_1 >= (eta_-) / C_"max"^+ [q_- (h - K) + (K' - b)], $
  obteniendo directamente la primera desigualdad del enunciado. Sustituyendo ahora $B_1 (K') = B_* - m_omega (h - K')$:
  $ u(c_0, L) + beta B_1 (K') <= hat(R) + beta B_* - m_omega (h - K) - (eta_-) / C_"max"^+ [(K' - b) + beta q_- (h - K')]. $
  Dado que $K' in [b, h)$ y $beta q_- < 1$, la combinación lineal en $K'$ cumple $(K' - b) + beta q_- (h - K') = (1 - beta q_-)(K' - b) + beta q_- (h - b) >= beta_- q_- (h - b)$, por lo que el último corchete queda acotado inferiormente por $Delta_2^"exact" = 0.2997787 > Delta_2 = 0.2997$. Por definición $hat(R) - Delta_2 + beta B_* = B_*$, concluyendo $u(c_0, L) + beta B_1 (K') <= B_1 (K)$ para todo $(K, K') in M^2$. En la caja $cal(P)$, $hat(R) - Delta_2 = -1.2957 < 0$ y $beta >= beta_- = 0.9699$ rinden $B_* <= -1.2957 \/ 0.0301 = -43.0465116$, mientras que $m_omega = (0.6999 times 0.9199) \/ 0.37495167 = 1.717123$ entrega $B_1 (b) <= -43.0465116 - 1.717123(0.18) = -43.355594$. Finalmente, como el consumo en el primer paso del testigo $c_M (K) = q_- K + F_(A_-) (K, 0.68) - 0.135$ cumple $0 < c_M (K) < min{1 - 0.68, C_"max"^+}$, la rama activa del mínimo en $eta$ lleva $eta_+$ (siendo $eta_- <= eta_+$ cota inferior válida) y $partial F_(A_-) \/ partial K > 0$, por lo que la derivada del piso del testigo verifica $W'_M (K) >= eta_- [q_- + partial F_(A_-) \/ partial K (K, 0.68)] \/ c_M (K) > m_omega = B'_1 (K)$ en todo $M$. Por lo tanto, $W_M (K) - B_1 (K)$ es estrictamente creciente y alcanza su ínfimo en $K = b = 0.10$: $inf_M (W_M - B_1) = W_M (0.10) - B_1 (0.10) = -35.57985494 - (-43.355594) > 7.775594$.
]

#thm_box("Teorema", "1", [Afilamiento analítico de un paso: reducción de $tau_H <= 46$ a $tau_H <= 23$])[
  Sea la barrera afín de un paso sobre $M = [0.10, 0.28)$ dada por:
  $ B_1 (K) = B_* - m_omega (h - K), #h(12pt) B_* = -43.0465116, #h(12pt) m_omega = (eta_- q_-) / C_"max"^+ = 1.717123. $
  Entonces $B_1 (K)$ es una sub-barrera global de permanencia certificada para toda trayectoria que permanece en $M$ bajo cualquier parámetro en $cal(P)$, con extremos $B_1 (0.10) = -43.355594$ y $B_1 (0.28) = -43.046512$. Comparada frente al testigo $W_M (0.10) = -35.57985494$ y al techo analítico $Psi^sharp (0.28)$:
  - El margen en el borde inferior aumenta desde $2.564$ hasta $W_M (0.10) - B_1 (0.10) >= 7.775594$ estado a estado (valor exacto $7.775739$; o $7.4665$ uniforme frente a $B_*$).
  - El plazo máximo de permanencia consecutiva en $M$ antes de alcanzar o superar $h = 0.28$ cae exactamente a la mitad: de *$tau_H <= 46$* a *$tau_H <= 23$* (con holgura positiva verificada en $T = 23$ igual a $+0.205614$, y $tau_H <= 24$ bajo cota uniforme independiente de $K_0$). Si $K_0 in [0.10, 0.105]$, vale además $3 <= tau_H <= 23$.
]

#proof_block(title: "Demostración del Teorema 1")[
  Consideremos cualquier trayectoria factible $x_0 -> x_1 -> dots -> x_T$ que permanezca en $M$ durante $T >= 1$ transiciones consecutivas ($x_t in M$ para $0 <= t <= T$), seguida de una continuación óptima desde $x_T$. Iterando la desigualdad de un paso del Lema 1 ($u(c_t, L_t) <= B_1 (x_t) - beta B_1 (x_(t+1))$) sobre $t = 0, dots, T - 1$ y acotando la continuación en $t = T$ por $V(x_T) <= Psi^sharp (x_T)$, el bienestar total $J_(x_0) (pi)$ cumple:
  $ J_(x_0) (pi) <= B_1 (x_0) + beta^T [Psi^sharp (x_T) - B_1 (x_T)]. $
  En $x in [0.10, 0.28)$, la derivada $(Psi^sharp)'(x) = 0.4 + 2.5 x^(-3\/2) >= 0.4 + 2.5 (0.28)^(-3\/2) = 17.272 > 2 > m_omega = B'_1 (x)$. Por lo tanto, $Psi^sharp (x_T) - B_1 (x_T)$ es estrictamente creciente en $x_T in [b, h)$ y alcanza su supremo en $x_T -> h^-$, acotado por $Psi^sharp (h) - B_* (beta) < -27.83 - B_* (beta)$. Sea $B_*^max := B_* (beta_-) = -43.0465116$; como $hat(R) - Delta_2 < 0$, vale $B_* (beta) <= B_*^max$ y por ende $(1 - beta) B_*^max >= (1 - beta) B_* (beta) = hat(R) - Delta_2$ para todo $beta in [beta_-, beta_+]$, de modo que $B_1 (K)$ con constante fija $B_*^max$ es igualmente sub-barrera válida en toda $cal(P)$. Reagrupando con $1 - beta^T > 0$ y $-27.83 - B_*^max > 0$:
  $ J_(x_0) (pi) <= (1 - beta^T) B_* (beta) - m_omega (h - x_0) + beta^T (-27.83) <= B_*^max - m_omega (h - x_0) + beta_+^T (-27.83 - B_*^max). $
  En la _cota uniforme_ ($T = 24$, acotando $-m_omega (h - x_0) <= 0$), resulta $J_(x_0) (pi) <= -43.0465116 + (0.9701)^24 (15.2165116) = -35.70287 < -35.58 <= W_M (x_0)$. En la _cota estado a estado_ ($T = 23$), como $W_M (x_0) - [B_*^max - m_omega (h - x_0)]$ es estrictamente creciente en $x_0 in [b, h)$ por el Lema 1, su mínimo se alcanza en $x_0 = b = 0.10$:
  $ W_M (x_0) - J_(x_0) (pi) &>= [W_M (0.10) - B_1 (0.10)] - beta_+^23 (-27.83 - B_*^max) \
  &>= 7.775594 - (0.9701)^23 (15.2165116) = +0.205614 > 0. $
  En consecuencia, ningún óptimo puede permanecer en $M$ durante $23$ períodos consecutivos ($tau_H <= 23$). Finalmente, la cota inferior $tau_H >= 3$ en $[0.10, 0.105]$ se mantiene intacta desde la tecnología productiva al verificarse dos pasos por debajo de $0.28$.
]

== Proposición 1 y Prueba Uniforme en $M_0 = [0.05, 0.10)$

Examinamos ahora la región previa de arranque $M_0 = [0.05, 0.10)$. Para cerrar el plazo uniforme hasta $b = 0.10$, acoplaremos la senda testigo en $M_0$ con el techo global certificado $Psi(0.10) = -35.166686$ (cuya síntesis LP y auditoría continua B&B 3D se desarrollan en la Sección 5.2, Proposición 3).

#thm_box("Proposición", "1", [Condición analítica en $M_0$ y testigo afilado con plazo $tau_(.1) <= 9$])[
  1. *(Condición exacta de monotonía en $eta$ y cota base $tau_(.1) <= 10$):* En $M_0 = [0.05, 0.10)$ con ocio positivo $L$, la derivada parcial de la utilidad instantánea respecto de $eta$ es $partial u \/ partial eta = log(c \/ (1 - L))$, por lo que la evaluación adversa en $(A_-, q_-, eta_+)$ requiere estrictamente *$c < 1 - L = 0.25$*. En los tres pasos del testigo base sobre $M_0$ ($0.05 -> 0.065 -> 0.0845 -> 0.100$ con $L = 0.75$), los consumos resultantes $[0.002495, 0.006286, 0.022068]$ satisfacen todos $c < 0.25$, arrojando $tau_(.1) <= 10$ ($J(10; 0.05) = -43.899678 < -43.844826 = W_(M_0) (0.05)$).
  2. *(Testigo afilado y extensión uniforme a todo $M_0$ con $tau_(.1) <= 9$):* Sustituyendo la senda anterior por la trayectoria suavizada de tres pasos $(K_0 -> 0.0595 -> 0.0755 -> 0.100)$ con esfuerzo $(0.45, 0.50, 0.60)$, cuyas utilidades de etapa en $(A_-, q_-, eta_+)$ son $[-3.681867, -3.888538, -3.828711]$ y cuyo piso vale $W_(M_0)^"sharp" (0.05) = -43.540132$, y acoplándola al techo de continuación $Psi(0.10) = -35.166686$ certificado en la Sección 5.2, el prefijo de $T = 9$ pasos cumple $J(9; 0.05) = -44.065405$, entregando holgura estrictamente positiva de $+0.525273$ (frente a la cola de referencia $W_M (0.10)$) y $+0.559826$ (frente al testigo CEGIS $W(0.10)$) uniformemente para todo $K_0 in [0.05, 0.10)$. En consecuencia, se certifica *$tau_(.1) <= 9$* en toda $M_0$.
]

#proof_block(title: "Demostración de la Proposición 1")[
  Aplicando el Lema 1 a $M_0 = [b_0, h_0) = [0.05, 0.10)$, la maximización sobre $L in [0, 1)$ rinde $C_"max,0"^+ = q_+ (0.10) + F_(A_+) (0.10, 1) - 0.05 = 0.100233$, $Delta_0^"exact" = (eta_- beta_- q_- dot 0.05) \/ C_"max,0"^+ = 0.311503 > Delta_0 = 0.3115$, $hat(R)_0 = -1.827$ y $B_*^((0), max) = (-1.827 - 0.3115) \/ (1 - beta_-) = -71.046512$ (con $B^((0)) (K_0) = B_*^((0)) - (eta_- q_-) \/ C_"max,0"^+ dot (0.10 - K_0)$ y pendiente constante $(B^((0)))'(K_0) = 6.4234$). Para el inciso (1), combinando la cota uniforme $B_*^((0), max) = -71.046512$ con el techo analítico de MR $Psi(0.10) = -34.271388$, el prefijo de $T = 10$ pasos rinde $J(10; 0.05) = B_*^((0), max) + beta_+^10 [Psi(0.10) - B_*^((0), max)] = -43.899678 < -43.844826 = W_(M_0) (0.05)$ (evaluado sobre el testigo base de $3$ pasos con $L = 0.75$, donde todo paso cumple $c < 1 - L = 0.25$, certificando $tau_(.1) <= 10$). Para el inciso (2), consideremos el testigo afilado $W_(M_0)^"sharp" (K_0)$ con liquidación temporal en un paso ($K_0 -> 0.0595$): el consumo de primera etapa $c_0^"sharp" (K_0) = q_- K_0 + F_(A_-) (K_0, 0.45) - 0.0595$ satisface $c_0^"sharp" (K_0) <= c_0^"sharp" (0.10^-) = 0.0822 < 1 - 0.45 = 0.55$ y $c_0^"sharp" (K_0) < C_"max,0"^+ = 0.100233$. Dado que $c_0^"sharp" < 1 - L$, la rama activa lleva $eta_+$, por lo que $eta_-$ proporciona la cota inferior de derivada:
  $ (W_(M_0)^"sharp")'(K_0) >= eta_- (q_- + F_(A,K)^(-) (K_0, 0.45)) / (c_0^"sharp" (K_0)) > (eta_- q_-) / C_"max,0"^+ = (B^((0)))'(K_0) = 6.4234 #h(8pt) forall K_0 in [0.05, 0.10), $
  donde $F_(A,K)^(-)$ denota $(partial F_(A_-)) / (partial K)$. Asimismo, sobre el techo $Psi$ certificado en la Sección 5.2, la auditoría exacta por intervalos `Decimal` de $50$ dígitos sobre $[0.05, 0.10]$ certifica $inf_(x in [0.05, 0.10)) Psi'(x) >= 91.23 > 6.4234 = (B^((0)))'(x)$, por lo que $Psi(x_9) - B^((0)) (x_9)$ es también estrictamente creciente en todo $M_0$ y alcanza su supremo exactamente en $x_9 -> 0.10^-$. En consecuencia, $W_(M_0)^"sharp" (K_0) - B^((0)) (K_0; beta_-)$ es estrictamente creciente en $[0.05, 0.10)$ y alcanza su ínfimo en $K_0 = 0.05$. Reagrupando como en el Teorema 1 con $Psi(0.10) = -35.166686$:
  $ W_(M_0)^"sharp" (K_0) - J(9; K_0) >= [W_(M_0)^"sharp" (0.05) - B^((0)) (0.05)] - beta_+^9 [Psi(0.10) - B_*^((0), max)] = +0.525273 > 0, $
  garantizando $tau_(.1) <= 9$ uniformemente sobre todo $M_0 = [0.05, 0.10)$ (combinado con la ausencia de salidas adversas por debajo de $0.05$, establecida en el Teorema 8 de MR (2026) y re-certificada continuamente hasta $b_"ext" = 0.0030$ en la Sección 5.2, Proposición 4).
]

La compresión posterior desde la cota analítica $tau_H <= 23$ hasta el límite de malla $tau_H^"VFI" = 4$ mediante la arquitectura CEGIS-LP determinista se presenta en la Sección 5.2 (Proposición 3 y Figura 3).

== Proposición 2 y Certificación Continua de Salidas Adversas (Tabla 2)

Para completar el certificado determinista analítico sin muestreo discreto, verificamos las cotas superiores globales de salida $E^+(K, a; l_0)$ que aparecen cuando el estado elegido $K'$ abandona una subregión por debajo de $a$ ($a = b = 0.10$ en $M$, $a = h = 0.28$ en $H_1 = [0.28, 0.80)$). Denotamos el recurso virtual mayorante por $cal(S)(K)$ para evitar toda colisión notacional con el umbral de Skiba $S_A$.

#thm_box("Proposición", "2", [Monotonía del Wronskiano y certificación de intervalos en salidas adversas])[
  Para todo par de umbral $(a, l_0)$ con consumo excedente $c_"sup" (K; a, l_0) = cal(S)(K) - a$, donde $cal(S)(K) = q_+ K + F_(A_+) (K, l_0) + (1 - l_0) t(K)$ y $t(K) = partial F_(A_+) \/ partial L (K, l_0) = 1.5 A_+ dot 2^(3\/2) K^(5\/2) l_0^(1\/2) (K + l_0)^(-5\/2)$, la función envolvente exacta de utilidad inmediata condicionada a no sobrepasar $a$ admite la forma cerrada autocontenida:
  $ E^+(K, a; l_0) = max_(eta in {eta_-, eta_+}) { eta log (c_"sup" (K; a, l_0) - t(K) omega^*(K, eta)) + (1 - eta) log omega^*(K, eta) }, $
  donde $omega^*(K, eta) = min{1, (1 - eta) c_"sup" (K; a, l_0) \/ t(K)}$ es la demanda óptima de ocio acotada por el límite unitario. En todo intervalo donde $omega^* < 1$, la identidad de la envolvente rinde exactamente:
  $ (d E^+) / (d K) = (cal(S)'(K)) / (cal(S)(K) - a) - (1 - eta) (5 l_0) / (2 K (K + l_0)). $
  Definida la ventaja puntual del testigo $Delta_X (K) := W_X (K) - [E^+(K, a; l_0) + beta_- Psi^sharp (a)]$ (nótese $beta_-$ al ser $Psi^sharp (a) < 0$) y el cociente $R_X (K) := (cal(S)(K) - a) \/ c_X (K)$, evaluando el Wronskiano continuo $Q_X (K) = cal(S)'(K) c_X (K) - c'_X (K)(cal(S)(K) - a)$ por aritmética de intervalos `Decimal` de $50$ dígitos sobre $M$ ($l_0 = 0.44$) y $H_1$ ($l_0 = 0.60, l_0 = 0.57$), se certifica $sup_M Q_M <= -0.04375 < 0$ (cotas superiores por subintervalo en $[-0.06341, -0.04375]$), $sup_(H_1) Q_(H_1) <= -0.13124 < 0$ (cotas superiores por subintervalo en $[-0.18976, -0.13124]$), $Delta'_M >= +0.0723 > 0$, $Delta'_(H_1) >= +0.0095 > 0$, y concavidad global $Delta''_M <= -2.5107 < 0$, $Delta''_(H_1) <= -0.1889 < 0$, alcanzando el mínimo exactamente en el borde izquierdo con márgenes $+0.094717$ en $K = 0.10$ y $+0.057148$ en $K = 0.28$.
]

#proof_block(title: "Demostración de la Proposición 2")[
  Sea $X in {M, H_1}$ con testigo $W_X (K) = u_"worst" (c_X (K), l_X) + beta_+ T_X$, consumo $c_X (K) = q_- K + F_(A_-) (K, l_X) - s_X > 0$, y parámetro tangente $l_0 >= sup(X)\/2$ ($0.44 >= 0.14$ en $M$ y $0.57 >= 0.40$ en $H_1$), condición suficiente para la dominancia global de la tangente en $L in [0, 1)$. Mediante intervalos `Decimal` de $50$ dígitos se verifica primero interioridad estricta del ocio óptimo de la envolvente en toda la región ($omega^*(K) in [0.5662, 0.6808] < 1$ en $M$ y $omega^*(K) in [0.4301, 0.5427] < 1$ en $H_1$), así como la dominancia estricta en la rama inferior de salida $s = 0$ ($W_X (K) - [E^+(K, 0; l_0) + beta_- Psi^sharp (0.05)] > 0$ uniformemente en $M$ y $H_1$). Como $t'(K) \/ t(K) = 5 l_0 \/ (2 K (K + l_0)) > 0$ y $(t'\/t)'(K) = -5 l_0 (2 K + l_0) \/ (2 K^2 (K + l_0)^2) < 0$, diferenciando cada rama de $W_X$ y $E^+$ mediante la envolvente en $omega^*(K) < 1$ se obtiene en todo punto suave (y para ambas derivadas laterales en los eventuales quiebres):
  $ Delta'_X (K) >= (eta_- c'_X (K) R_X (K) - cal(S)'(K)) / (cal(S)(K) - a) + (1 - eta_+) (5 l_0) / (2 K (K + l_0)), #h(10pt) R_X (K) := (cal(S)(K) - a) / (c_X (K)) > 1. $
  La derivada del cociente verifica $R'_X (K) = Q_X (K) \/ c_X (K)^2$ con Wronskiano $Q_X (K) := cal(S)'(K) c_X (K) - c'_X (K)(cal(S)(K) - a)$, cuya derivada $Q'_X (K) = cal(S)''(K) c_X (K) - c''_X (K)(cal(S)(K) - a)$ cancela el término $cal(S)' c'_X$. Acotando $|Q'_X|$ en cada subintervalo $[k_L, k_R]$ mediante los extremos y los picos únicos de $|F_(A, K thin K)|$ y $|t''|$, la forma centrada arroja $Q_M <= -0.04375 < 0$ en los $4$ subintervalos de $M$ y $Q_(H_1) <= -0.13124 < 0$ en los $6$ subintervalos de $H_1$. Así $R_X (K)$ es estrictamente decreciente en todo $X$, rindiendo $inf_M Delta'_M >= +0.0723 > 0$ e $inf_(H_1) Delta'_(H_1) >= +0.0095 > 0$ (sin mínimos interiores). Además, en las regiones suaves:
  $ Delta''_X (K) <= ((cal(S)')^2 - eta_- (c'_X R_X)^2) / ((cal(S) - a)^2) + (eta_plus.minus c''_X) / c_X - (cal(S)'') / (cal(S) - a) + (1 - eta_+) (t' / t)'(K), $
  evaluando $eta c''_X \/ c_X$ en $eta_+$ cuando $c''_X > 0$ (en $[0.10, l_M\/4 = 0.17)$) y en $eta_-$ cuando $c''_X <= 0$. La partición en $8$ subintervalos de $M$ y $10$ de $H_1$ certifica $Delta''_M <= -2.5107 < 0$ y $Delta''_(H_1) <= -0.1889 < 0$. Los dos únicos quiebres en $H_1$ —en $k_W = 0.406819$ donde $c_(H_1) (K) = 1 - l_H$ ($W'_(H_1)$ cae de $3.954006$ a $3.952877$) y en $k_E = 0.573570$ donde $(-E^+)'$ cae de $-1.652310$ a $-1.652744$— son ambos quiebres hacia abajo que preservan la concavidad global de $Delta_X$. Por ende, $Delta'_X$ alcanza su ínfimo en el borde derecho ($Delta'_M (0.28^-) = +0.502666$, $Delta'_(H_1) (0.80^-) = +0.100489$) y $Delta_X$ alcanza su mínimo en el borde izquierdo: $+0.094717$ en $K = 0.10$ ($+0.062495$ frente al techo analítico $Psi$ de MR sin desplazamiento) y $+0.057148$ en $K = 0.28$ con $l_0 = 0.57$ ($+0.024926$ frente a $Psi$ sin desplazamiento).
]

La Tabla 2 resume la auditoría cuantitativa de intervalos de la Proposición 2 en los extremos regionales comparando frente a $Psi^sharp$ y al techo analítico sin desplazamiento $Psi$ (frente a la súper-barrera CEGIS-LP $Psi$ de la Sección 5.2 en $p = 0\%$, los márgenes ascienden a $+0.787$ en $M$ y $+0.236$ en $H_1$).

#figure(
  table(
    columns: (1.10fr, 0.80fr, 1.10fr, 1.10fr, 1.95fr),
    inset: 6pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.6pt)[Región],
      text(fill: white, weight: "bold", size: 8.6pt)[Política $l_0$],
      text(fill: white, weight: "bold", size: 8.6pt)[Wronskiano $sup Q$],
      text(fill: white, weight: "bold", size: 8.6pt)[Cota $inf Delta'$],
      text(fill: white, weight: "bold", size: 8.6pt)[Margen ($W - E^+ - beta_- Psi$)],
    ),
    [$M = [0.10, 0.28)$], [$0.44$], [$-0.04375 < 0$], [$+0.0723 > 0$], [$+0.0947$ ($Psi^sharp$) / $+0.0625$ ($Psi$)],
    [$H_1 = [0.28, 0.80)$], [$0.60$], [$-0.12362 < 0$], [$+0.0118 > 0$], [$+0.0561$ ($Psi^sharp$)],
    [$H_1 = [0.28, 0.80)$], [$0.57$], [$-0.13124 < 0$], [$+0.0095 > 0$], [$+0.0571$ ($Psi^sharp$) / $+0.0249$ ($Psi$)],
  ),
  caption: [Tabla 2: Auditoría por intervalos (50 dígitos) de las condiciones del Wronskiano y márgenes de salida adversa frente a los techos analíticos $Psi^sharp$ y $Psi$.],
)

// ============================================================================
// SECCIÓN 4: EQUIVALENCIA ASINTÓTICA (A -> INFINITO) Y LEY DE SEGUNDO ORDEN
// ============================================================================
= Equivalencia Asintótica bajo Escalamiento ($A -> oo$) y Ley de Segundo Orden

Abordamos ahora el problema asintótico de determinar si el modelo completo con trabajo endógeno $L_t in [0, 1)$ exhibe la misma ley de potencia que el modelo simplificado con trabajo fijo en $overline(L) = 1$ cuando $A -> oo$. Denotemos $S_A$ el umbral de Skiba bajo trabajo endógeno (único bajo $beta theta > 1$), y $S_A^"fix" (overline(L))$ el umbral análogo bajo oferta fija $L_t equiv overline(L)$. Definimos $d = -rho > 0$, el exceso de homogeneidad (exponente de rendimientos crecientes a escala) $r = theta - 1 in (0, 1)$ (con $theta = 3\/2$, $r = 1\/2$ en la parametrización CES armónica $d = 1$), $c_K = w^(theta\/rho) = 2^(3\/2) approx 2.828427$, $c_w = (1 - w)\/w = 1$, $nu = (1 - eta)\/eta$, y el capital estacionario de referencia $K_"ss" (A)$ donde $F_(A,K) (K_"ss", 1) = D = 1\/beta - q$. Conviene precisar la distinción entre dos regímenes de escala: el comportamiento $L_t -> 0$ del Teorema 2 (Parte 1) rige exclusivamente en el régimen reescalado de cuello de botella $K_t = Theta(A^(-1\/r))$ alrededor del umbral de trampa, mientras que una vez alcanzado el estado estacionario alto en la meseta macroscópica ($K_t = Theta(A^(1\/r))$), la oferta laboral converge al límite interior $L_"ss" = theta eta \/ (theta eta + 1 - eta) = 7\/9$ (Tabla 3).

== Teorema 2 (Parte 1) y Corolario 1 ($beta theta > 1$)

#thm_box("Teorema", "2", [Parte 1: Convergencia uniforme hacia la ley de potencia asintótica])[
  Fijemos los parámetros primitivos distintos de $A$ en la región paciente con $d = -rho > 0$, $r = theta - 1 in (0, 1)$ y $beta theta > 1$. Sea $c_K = lim_(k -> 0^+) F_1 (k, 1)\/k^theta = w^(theta\/rho) = 2^(3\/2)$. Reescalando $K_t = A^(-1\/r) k_t$ y $C_t = A^(-1\/r) c_t$ con $k_t, c_t = Theta(1)$, a lo largo de toda acción óptima interior la oferta laboral y la razón capital--trabajo obedecen:
  $ L_t = Theta(A^(-d\/(r(1+d)))) -> 0, #h(12pt) K_t / L_t = Theta(A^(-1\/(r(1+d)))) -> 0 #h(8pt) (A -> oo). $
  En consecuencia, la desutilidad del ocio se anula como $(1 - eta)|log(1 - L_t)| = O(A^(-d\/(r(1+d)))) -> 0$ y ambos umbrales críticos normalizados convergen al límite físico de reposición común $(delta\/c_K)^(1\/r)$ para todo $overline(L) in (0, 1]$:
  $ lim_(A -> oo) A^(1\/r) S_A^"fix" (overline(L)) = lim_(A -> oo) A^(1\/r) S_A = (delta / c_K)^(1\/r), #h(12pt) lim_(A -> oo) (S_A) / (S_A^"fix" (overline(L))) = 1. $
  En la calibración estándar ($theta = 3\/2$, $r = 1\/2$, $delta = 0.08$, $c_K = 2^(3\/2)$), este límite es exactamente $(delta\/c_K)^2 = 0.000800$.
]

#proof_block(title: "Demostración del Teorema 2, Parte 1")[
  Con $K = A^(-1\/r) k$ y $C = A^(-1\/r) c$ ($r = theta - 1$, $rho = -d < 0$), el producto normalizado vale:
  $ f_A (k, L) := A^(1\/r) F_A (A^(-1\/r) k, L) = c_K k^theta [1 + c_w (k / (A^(1\/r) L))^d]^(-theta\/d), #h(10pt) c_w = (1 - w) / w. $
  Con trabajo fijo $L equiv overline(L) in (0, 1]$, $(A^(1\/r) overline(L))^(-d) = O(A^(-d\/r)) -> 0$ y $f_A (k, overline(L)) -> c_K k^theta$. Con trabajo endógeno, multiplicando la condición de primer orden $F_(A,L) (K, L) = nu C \/ (1 - L)$ por $A^(1\/r)$ resulta:
  $ theta c_K c_w k^(theta + d) A^(-d\/r) L^(-1 - d) [1 + c_w ((A^(1\/r) L) / k)^(-d)]^(-1 - theta\/d) = (nu c) / (1 - L), $
  lo cual fuerza $L = [theta c_K c_w k^(theta + d) \/ (nu c)]^(1\/(1+d)) A^(-d\/(r(1+d))) (1 + o(1)) -> 0$ y $K\/L = Theta(A^(-1\/(r(1+d)))) -> 0$. Para demostrar la convergencia de las fronteras mismas, fijemos cualquier $k_0 > (delta\/c_K)^(1\/r)$, sea $K_0 = A^(-1\/r) k_0$, y construyamos una expansión factible en tres fases manteniendo trabajo constante $L_0$ ($L_0 = 3\/4$ en el problema endógeno; $L_0 = 1$ o $overline(L)$ en trabajo fijo):
  - _Fase I (escape del cuello de botella):_ Eligiendo $epsilon.alt_1 in (0, 1)$ con $c_K (1 - epsilon.alt_1) k_0^r > delta$ y un umbral macroscópico fijo $K_"esc" > 0$ suficientemente pequeño para tener $f_A (k, L_0) >= c_K (1 - epsilon.alt_1\/2) k^theta$ en $K_t <= K_"esc"$, consumir la mitad del excedente neto sobre $k_t$ alcanza en $T_1 (k_0) < oo$ pasos (independientes de $A$) un nivel $k_(T_1) >= k_1 := max{2, (2\/[c_K (1 - epsilon.alt_1\/2)])^(1\/(theta - tilde(theta)))}$ donde $tilde(theta) in (beta^(-1), theta)$ existe por $beta theta > 1$.
  - _Fase II (crecimiento superexponencial):_ Indexando por $j >= 0$ a partir de $T_1$ y ahorrando $K_(T_1+j+1) = [q K_(T_1+j) + F_A (K_(T_1+j), L_0)]\/2$, por inducción $k_(T_1+j) >= 2^(tilde(theta)^j)$ y $k_(T_1+j+1) >= k_(T_1+j)^(tilde(theta)) >= 2^(tilde(theta)^(j+1))$, superando $K_"esc"$ en a lo sumo $J(A) <= (log log A)\/(log tilde(theta)) + O(1)$ pasos (en el último salto se ahorra exactamente $K_(T_1+J+1) = K_"esc"$).
  - _Fase III (meseta macroscópica):_ Mantener $K_"esc"$ rinde consumo $A F_1 (K_"esc", L_0) - delta K_"esc" = Omega(A)$ y utilidad descontada al menos $beta^(T_1+J+1) eta\/(1 - beta) dot log A - O(1)$.
  Como durante las Fases I--II el consumo $C_t = Omega(A^(-1\/r))$ aporta utilidad acumulada al menos $-(1 - beta^(T_1+J+1)) eta\/(r(1 - beta)) dot log A - O(1)$, mientras que por cota de recursos toda senda confinada en $(0, K_0]$ (incluido cualquier óptimo que se extingue) tiene valor acotado por $-eta\/(r(1 - beta)) dot log A + O(1)$, el término dominante $-eta\/(r(1 - beta)) dot log A$ se cancela exactamente y el excedente neto escala al menos como:
  $ beta^(T_1 + J(A) + 1) (theta eta) / (r(1 - beta)) log A - O(1) >= c_1 (log A)^(1 - |log beta| \/ log tilde(theta)) - O(1) -> +oo, $
  pues $beta tilde(theta) > 1 ==> 1 - |log beta| \/ log tilde(theta) > 0$. Por contradicción, ningún óptimo puede extinguirse desde $K_0 = A^(-1\/r) k_0$ para $A$ grande, probando $limsup_(A -> oo) A^(1\/r) S_A <= (delta\/c_K)^(1\/r)$; combinando con la cota física inferior $A^(1\/r) kappa_A -> (delta\/c_K)^(1\/r)$ queda demostrado el límite común.
]

#thm_box("Corolario", "1", [Extensión y unicidad en el régimen de paciencia débil $beta theta > 1$])[
  Supóngase únicamente $beta in (0, 1)$ y *$beta theta > 1$*, sin exigir la condición más fuerte de paciencia local $beta [q + theta delta] > 1$. Definidos los umbrales generales $S_A^- := inf{K_0 > 0 : "algún óptimo desde " K_0 " sobrevive"}$ y $S_A^+ := sup{K_0 > 0 : "algún óptimo desde " K_0 " se extingue"}$, se cumple $kappa_A <= S_A^- <= S_A^+$, ambos convergen al mismo límite físico $(delta\/c_K)^(1\/r)$ cuando $A -> oo$, y para todo $A$ suficientemente grande existe un único punto de Skiba $S_A^- = S_A^+ = S_A$. Verificamos numéricamente el Corolario en $beta = 0.90$ ($beta theta = 1.35 > 1$, $(D\/c_K)^2 = 0.004565$): entre $A = 1.5$ y $A = 10^8$, la razón $S_A \/ S_A^"fix" (1)$ cae monótonamente de $1.05629$ a $1.00191$ ($A^2 S_A^"fix" (1) = 0.001714 < A^2 S_A = 0.001717 < 0.004565$).
]

#proof_block(title: "Demostración del Corolario 1")[
  Para todo $beta in (0, 1)$, el confinamiento al compacto $[0, K_"max" (K_0, A)]$ asegura existencia de óptimos y continuidad de $V_A (K)$. Para trasladar el argumento de cruce único al régimen $beta theta > 1$ verificamos tres eslabones explícitos sobre los objetos definidos en la Sección 3.1:
  1. *(Ancla productiva en $b_A$ y supermodularidad local en $(0, b_A]$):* Fijando $b_A := (delta\/c_K + 1)^(1\/r) A^(-1\/r)$ (de orden $Theta(A^(-1\/r))$), para todo $A$ suficientemente grande se cumplen las cotas locales de cruce $L\/K > c$ sobre $(0, b_A]$ que garantizan tanto la sub-optimalidad del trabajo nulo como la positividad de la derivada cruzada $r_("red", K s) > 0$. Paralelamente, la expansión en tres fases del Teorema 2 (Parte 1) desde $b_A$ entrega un umbral productivo $Omega((log A)^(1 - tilde(kappa)))$ sobre la referencia $-eta\/(r(1-beta)) log A$, estableciendo $S_A^+ <= b_A$. Más aún, ninguna senda óptima que se extingue desde $K_0 <= b_A$ puede salir a $[b_A, oo)$ y regresar: si lo hiciera, en el último instante $T := sup{t >= 0 : K_t >= b_A}$ tendría $K_(T+1) < b_A$ y continuación extinta acotada por $O(1)$ sobre $-eta\/(r(1-beta)) log A$, perdiendo $Omega((log A)^(1 - tilde(kappa)))$ frente a ejecutar la expansión desde $K_T >= b_A$; por monotonicidad, toda trayectoria extinta desde $K_0 <= b_A$ queda confinada en $(0, K_0]$.
  2. *(Exclusión de óptimos estacionarios cuando $E = D - theta delta >= 0$):* Cuando $E < 0$, el margen $D < theta delta$ descarta raíces estacionarias interiores en $(0, b_A]$; cuando $E >= 0$ (como ocurre en $beta = 0.90$, donde $E = +0.0089 > 0$), la ecuación de Euler sí admite un candidato estacionario interior $K_"stat" (A) = (D \/ (theta c_K))^(1\/r) A^(-1\/r) (1 + o(1))$. Distinguimos dos subcasos:
     - Si $E = D - theta delta > 0$, entonces $D\/theta > delta$, de modo que $(D\/(theta c_K))^(1\/r) > (delta\/c_K)^(1\/r)$ y existe $epsilon.alt_2 > 0$ independiente de $A$ tal que $K_"stat" (A) > [(delta\/c_K)^(1\/r) + epsilon.alt_2] A^(-1\/r)$ para todo $A$ suficientemente grande; aplicando la construcción en tres fases del Teorema 2 (Parte 1) desde $K_0 = K_"stat" (A)$, la ganancia de escape respecto de la senda estacionaria diverge a $+oo$ sobre el término base $-eta\/(r(1 - beta)) log A + O(1)$.
     - En el caso borde $E = 0$ ($D = theta delta$), aunque $A^(1\/r) K_"stat" (A) = (delta\/c_K)^(1\/r) + Theta(A^(-d\/r))$, combinando las condiciones estacionarias $F_(A, K) = theta delta$ y $F_(A, L) = nu C\/(1 - L)$ resulta $L_"stat" = theta eta \/ (theta eta + 1 - eta) = Theta(1)$ y $C_"stat" \/ K_"stat" = delta c_w (K_"stat" \/ L_"stat")^d = Theta(A^(-d\/r)) -> 0$ (y análogamente bajo trabajo fijo $overline(L)$). En consecuencia, la trayectoria estacionaria rinde utilidad $-eta(1 + d)\/(r(1 - beta)) log A + O(1)$, estrictamente dominada por _cake-eating_ puro $-eta\/(r(1 - beta)) log A + O(1)$ para todo $A$ grande.
     En ambos casos $K_"stat" (A) in.not G_A (K_"stat" (A))$, probando que todo óptimo en $(0, S_A^+]$ converge asintóticamente a $0$ o escapa de $(0, b_A]$.
  3. *(Regularidad local, envolvente de Milgrom--Segal y unicidad $S_A^- = S_A^+$):* Sea $V_"surv" (K)$ (resp. $V_"ext" (K)$) el supremo del problema restringido a trayectorias con $liminf_(t -> oo) K_t > 0$ (resp. $K_t -> 0$). En cualquier vecindad de un punto de indiferencia $K in [S_A^-, S_A^+] subset (kappa_A, b_A]$, todo sucesor extinto $s in G^-(K)$ y todo sucesor de supervivencia $s' in G^+(K)$ satisfacen $s' > K >= s$ (por monotonía y ausencia de óptimos estacionarios), con correspondencias compactas y funciones valor continuas. Aplicando el teorema de la envolvente direccional de Milgrom y Segal (2002), la derivada lateral izquierda de $V_"surv"$ y la derivada lateral derecha de $V_"ext"$ satisfacen la identidad exacta:
     $ V'_("surv") (K^-) = min_(s in G^+(K)) partial_K u_"red" (K, s) > max_(s in G^-(K)) partial_K u_"red" (K, s) = V'_("ext") (K^+), $
     donde la desigualdad estricta proviene de las diferencias crecientes estrictas $r_("red", K s) > 0$, impidiendo un segundo cruce descendente de $V_"surv" - V_"ext"$ y forzando $S_A^- = S_A^+ = S_A$ para todo $A$ suficientemente grande.
]

== Isomorfismo Finito, Demostración Analítica Pura de $S_A^"fix" (1) < S_A$ y Ley de Segundo Orden

El siguiente paso relaciona ambos problemas para productividad $A$ _finita_ arbitraria mediante un isomorfismo exacto de escalamiento y cierra analíticamente $S_A^"fix" (1) < S_A$ sin depender de verificación numérica.

#thm_box("Teorema", "2", [Parte 2: Isomorfismo finito y prueba analítica pura de $S_A^"fix" (1) < S_A$])[
  1. *(Isomorfismo de oferta fija arbitraria):* Para todo $A > 0$ y todo nivel constante de trabajo $overline(L) in (0, 1]$, la homogeneidad grado $theta = 1 + r$ de $F_A (K, L)$ junto con el reescalamiento $tilde(K)_t = K_t \/ overline(L)$ inducen el isomorfismo exacto con la economía de capacidad plena ($overline(L) = 1$) a productividad $A overline(L)^r$:
     $ S_A^"fix" (overline(L)) = overline(L) thin S_(A overline(L)^r)^"fix" (1), #h(12pt) kappa_A^"fix" (overline(L)) = overline(L) thin kappa_(A overline(L)^r) >= kappa_A^"fix" (1) = kappa_A. $
  2. *(Criterio variacional y desigualdad estricta analítica $S_A^"fix" (1) < S_A$):* Evaluando ambos problemas en el punto de Skiba endógeno $S_A$, sea la prima de bienestar de capacidad plena frente al óptimo endógeno:
     $ Delta W_A^+ := V_A^"fix" (S_A; 1) - V_A^"endo" (S_A) >= Delta W_A^(pi^+) := J_A^"fix" (S_A; pi^+ |_(L=1)) - V_A^"endo" (S_A) > 0, $
     donde $pi^+ = (K_t^+, L_t^+)$ denota un óptimo productivo que escapa desde $K_0^+ = S_A$, y sea $Delta W_A^- := sup_(pi^- in cal(O)_-^"fix") [J_A^"fix" (pi^-) - V_A^"endo" (S_A)] = O(A^(-d\/(r(1+d))))$ la cota en trayectorias confinadas en $(0, S_A]$. Fijado cualquier $tilde(theta) in (beta^(-1), theta)$ como en la Parte 1, con $tilde(kappa) := (|log beta|) / (log tilde(theta)) in (kappa, 1)$ y $M = 2(1 + tilde(kappa))(1 + d)\/d$, para todo $A$ suficientemente grande el tiempo hasta alcanzar $k_t^+ >= (log A)^M$ a lo largo de $pi^+$ satisface la cota log-logarítmica pura:
     $ T_M (A) <= (1 + tilde(kappa)) / (|log beta|) log log A + O(1), #h(12pt) tilde(kappa) = (|log beta|) / (log tilde(theta)) in (kappa, 1). $
     En el instante $t^* = T_M (A)$, la ganancia intramarginal en $L = 1$ satisface $Delta W_A^(pi^+) >= beta^(T_M) g_(T_M) >= c_(10) A^(-d\/(r(1+d))) (log A)^(1 + tilde(kappa)) >> O(A^(-d\/(r(1+d)))) = Delta W_A^-$. En consecuencia, existe un umbral explícito $A_0$ tal que para *todo* $A >= A_0$ se cumple estrictamente *$S_A^"fix" (1) < S_A$* por demostración analítica pura.
]

#proof_block(title: "Demostración del Teorema 2, Parte 2")[
  La homogeneidad de grado $theta = 1 + r$ rinde $F_A (overline(L) tilde(K), overline(L)) = overline(L) F_(A overline(L)^r) (tilde(K), 1)$ y $eta log(overline(L) tilde(C)_t) = eta log tilde(C)_t + eta log overline(L)$, estableciendo el isomorfismo finito. En $K_0 = S_A$, existen tanto un óptimo productivo $pi^+$ como un óptimo extinto alcanzando $V_A^"endo" (S_A)$. Para las trayectorias confinadas $pi^- in cal(O)_-^"fix"$ bajo $K_t^"f" <= S_A <= c_+ A^(-1\/r)$, comparando $V_A^"fix" (K_t^"f"; 1)$ con el piso _cake-eating_ se deduce $C_t^"f" \/ K_t^"f" >= chi_p^"fix" = Omega(1) > 0$; equipando $(K_t^"f")$ con trabajo $tilde(L)_t = c_0 A^(-d\/(r(1+d)))$ la pérdida CES y el costo de ocio rinden $(F_A (K_t^"f", 1) - F_A (K_t^"f", tilde(L)_t)) \/ C_t^"f" = O(A^(-d\/(r(1+d))))$ y $Delta W_A^- = O(A^(-d\/(r(1+d))))$. Restando al valor normalizado $v_A (k) := V_A (A^(-1\/r) k) + eta\/(r(1-beta)) log A$, basta probar $Delta W_A^(pi^+) >> A^(-d\/(r(1+d)))$ en cuatro eslabones analíticos puros:
  1. *(Invariancia de $[0, k_*]$ y salida $T_epsilon.alt (A) <= |log beta|^(-1) log log A + O(1)$):* Puesto que $k_0^+ = A^(1\/r) S_A > (delta\/c_K)^(1\/r) =: k_*$ para $A$ grande y cualquier trayectoria en $[0, k_*]$ con $k_(t+1) <= k_*$ es no creciente en $K_t$ (lo que acota su valor normalizado por $v^"cake" (k_*) + O(1)$), el óptimo productivo $pi^+$ satisface $k_t^+ > k_*$ para todo $t >= 0$. Fijemos $epsilon.alt > 0$ suficientemente pequeño tal que en $k in (k_*, k_* + epsilon.alt]$ el consumo máximo compatible con permanecer en $(k_*, k_* + epsilon.alt]$ cumpla $eta log macron(c)(epsilon.alt) <= (1 - beta) v^"cake" (k_*) - 1$. Si $pi^+$ demora $T_epsilon.alt (A) := inf{t >= 0 : k_t^+ > k_* + epsilon.alt}$ pasos dentro de $(k_*, k_* + epsilon.alt]$, iterar Bellman hasta $T_epsilon.alt$ da $v^"cake" (k_*) <= v_A^"endo" (k_0^+) <= (1 - beta^(T_epsilon.alt))(v^"cake" (k_*) - 1\/(1-beta)) + beta^(T_epsilon.alt) v_A^"endo" (k_(T_epsilon.alt)^+)$. Como $v_A^"endo" (k_(T_epsilon.alt)^+) <= C_0 log A + O(1)$, se obtiene $beta^(T_epsilon.alt (A)) [C_0 log A + O(1)] >= 1$, implicando $T_epsilon.alt (A) <= |log beta|^(-1) log log A + O(1)$.
  2. *(Piso de bienestar en $k_* + epsilon.alt$ vía crecimiento doblemente exponencial):* Desde cualquier estado $k >= k_* + epsilon.alt$, la política de Fases I--III de la Parte 1 alcanza escala macroscópica en $T_1 (epsilon.alt) + |log tilde(theta)|^(-1) log log A$ pasos (con $beta tilde(theta) > 1$), entregando el piso $v_A^"endo" (k_* + epsilon.alt) >= c_1 (log A)^(1 - tilde(kappa)) - C_2$, donde $tilde(kappa) = |log beta| \/ log tilde(theta) in (kappa, 1)$.
  3. *(Acotación de $T_M (A)$ entre $k_* + epsilon.alt$ y $(log A)^M$):* Sea $T_M (A) := inf{t >= 0 : k_t^+ >= (log A)^M}$ con $M = 2(1 + tilde(kappa))(1 + d)\/d$. Mientras $k_t^+ < (log A)^M$, la utilidad normalizada instantánea verifica $u_"norm" (k_t^+, L_t^+) <= eta log(q k_t^+ + c_K (k_t^+)^theta) <= eta theta M log log A + C_3$, mientras que $v_A^"endo" (k_(T_M)^+) <= C_4 log A$. Iterando Bellman entre $T_epsilon.alt$ y $T_M$: $c_1 (log A)^(1 - tilde(kappa)) - C_2 <= eta theta M (log log A)\/(1 - beta) + beta^(T_M - T_epsilon.alt) C_4 log A$, lo cual fuerza $beta^(T_M - T_epsilon.alt) >= c'_6 (log A)^(-tilde(kappa))$ y, combinando con el Eslabón 1, *$T_M (A) <= (1 + tilde(kappa)) / (|log beta|) log log A + O(1)$* y $beta^(T_M (A)) >= c_6 (log A)^(-1 - tilde(kappa))$.
  4. *(Ganancia instantánea en $t^* = T_M (A)$):* En el primer instante de alcance $t^* = T_M (A)$ se cumple $k_(t^*)^+ >= (log A)^M$, de modo que $K_(t^*)^+ >= A^(-1\/r) (log A)^M$; además, como $k_(t^* - 1)^+ < (log A)^M$, vale también $K_(t^*)^+ <= q K_(t^* - 1)^+ + F_A (K_(t^* - 1)^+, 1) <= A^(-1\/r) [q (log A)^M + c_K (log A)^(M theta)] -> 0$, lo que justifica $F_1 (K_(t^*)^+, 1) asymp (K_(t^*)^+)^theta$ y $q K_(t^*)^+ \/ (A (K_(t^*)^+)^theta) = (k_(t^*)^+)^(-r) <= (log A)^(-M r) -> 0$, acotando el consumo por $C_(t^*)^+ <= C_5 A F_1 (K_(t^*)^+, 1)$. Sea $L_"cut" := min{1\/2, (K_(t^*)^+)^(d\/(1+d))}$. Si $L_(t^*)^+ >= L_"cut"$, suprimir el ocio aporta $(1 - eta)|log(1 - L_(t^*)^+)| >= (1 - eta) L_"cut" >= c_7 min{1, A^(-d\/(r(1+d))) (log A)^(M d\/(1+d))}$. Si $L_(t^*)^+ < L_"cut"$, entonces $K_(t^*)^+ \/ L_(t^*)^+ > (K_(t^*)^+)^(1\/(1+d))$ y, combinando la monotonía CES con la desigualdad elemental $log(1 + x) >= (log 2) min{1, x}$ para todo $x >= 0$, la ganancia de consumo $eta log(1 + [F_A (K_(t^*)^+, 1) - F_A (K_(t^*)^+, L_(t^*)^+)] \/ C_(t^*)^+)$ satisface $(F_A (K, 1) - F_A (K, L_(t^*)^+)) \/ C_(t^*)^+ >= c_8 min{1, (K_(t^*)^+ \/ L_(t^*)^+)^d} \/ C_5$ y por tanto $g_(t^*) >= c_9 min{1, (K_(t^*)^+)^(d\/(1+d))}$. Ambos casos garantizan $g_(t^*) >= c'_9 min{1, A^(-d\/(r(1+d))) (log A)^(M d\/(1+d))}$. Sustituyendo $M = 2(1+tilde(kappa))(1+d)\/d$ ($M d \/ (1 + d) = 2(1 + tilde(kappa))$), resulta:
     $ Delta W_A^+ >= Delta W_A^(pi^+) >= beta^(T_M (A)) g_(T_M (A)) >= c_(10) A^(-d\/(r(1+d))) (log A)^(1 + tilde(kappa)) >> O(A^(-d\/(r(1+d)))) = Delta W_A^-, $
     cerrando analíticamente $S_A^"fix" (1) < S_A$ para todo $A$ suficientemente grande.
]

#obs_box("1", [Ley asintótica de segundo orden: Parte 1 y cota superior de Parte 2 formalizadas en Lean 4; cota inferior de Parte 2 heurística hasta $A = 10^8$])[
  Sea $k_* := (delta\/c_K)^(1\/r)$, $lambda_K := q + theta delta > 1$ el valor propio de expansión linealizada alrededor de $k_*$, $mu_K := |log beta| \/ log lambda_K$ y $kappa = |log beta| \/ log theta$. Al equilibrar la pérdida logarítmica inicial de permanencia cerca de $k_*$ frente a la recompensa productiva futura:
  $ (eta) / (1 - beta) log(k_* / Delta_k) + C_0 approx Delta_k^(mu_K) [C_oo (log A)^(1 - kappa) + C_"const"], $
  donde $C_"const" approx |v^"cake" (k_*)|$ recoge la constante de nivel de _cake-eating_, emergen dos resultados cuantitativos (cuyo esquema de demostración completo, definiendo el reescalado $y_t = alpha^(1\/r) k_t$, la política linealizada explícita $c_t^*$, la coordenada cuadrática sub-linealizada $phi(x) = x - C x^2$ y la fracción de consumo $phi.alt(Delta_k) asymp (log log A)^(-1)$, se detalla en el Apéndice A.5 y se formaliza en `MVS/Theorem2SecondOrder.lean`):
  1. *(Convergencia ultraslow de segundo orden — demostrada y formalizada en Lean 4):* El desvío $Delta_k (A) := A^(1\/r) S_A - k_*$ satisface rigurosamente $Delta_k (A) asymp ([log log A] \/ [(log A)^(1 - kappa)])^(1\/mu_K)$ para todo $beta theta > 1$, siendo $phi.alt(Delta_k)$ subdominante como $O(log log log A)$ frente a $log log A$ en la inversión de primer orden. En nuestra calibración ($lambda_K = 1.04$, $mu_K = 0.77661$, $kappa = 0.07512$, $(1 - kappa)\/mu_K = 1.19092$, $1\/mu_K = 1.28765$), el gran desplazamiento constante $C_"const" approx 336$ actúa como freno pre-asintótico junto al exponente moderado $1 - kappa = 0.9249$, explicando por qué en $A = 10^8$ persiste aún un $+3.9\%$ ($A^2 S_A = 0.000831$ frente a $0.000800$).
  2. *(Brecha relativa por envolvente de Milgrom--Segal — cota superior formalizada en Lean 4; cota inferior heurística):* Del solo término $t = 0$ del presupuesto telescópico en $phi(x)$ se obtiene $c_0 <= 2 lambda_K Delta_k$, rindiendo rigurosamente la cota superior $(S_A - S_A^"fix" (1)) \/ S_A <= (8\/(eta k_*)) Delta_k (A) Delta W_A^+ = O((log log A)^(1 + 1\/mu_K) \/ (log A)^(1 + (1 - kappa)\/mu_K))$. En la cota inferior (heurística), el factor $phi.alt(Delta_k) asymp (log log A)^(-1)$ sí sobrevive en primer orden en la pendiente envolvente, explicando la deriva suave de la razón $(S_A - S_A^"fix" (1)) \/ (S_A dot Delta_k dot Delta W_A^+)$ en la Tabla 3 ($29.35$ en $A = 10^2$ a $22.36$ en $A = 10^8$).
]

La Tabla 3 y la Figura 1 reportan la verificación VFI continua en malla logarítmica refinada en $k = A^2 K$ desde $A = 0.75$ hasta $A = 10^8$ (alcanzando capitales estacionarios del orden de $k_"ss" tilde.op A^(5\/2) = 10^(20)$ sin truncamiento de grilla), confirmando en todas las filas: (i) $0 < Delta W_A^(pi^+) <= Delta W_A^+$; (ii) decaimiento polilogarítmico $Delta W_A^+ = Theta((log log A)\/(log A))$ con $T_"esc" (A)$ creciendo de $97$ a $126$ y $Delta_k$ descendiendo de $0.000052$ ($10^2$) a $0.000031$ ($10^8$); (iii) convergencia exacta del trabajo estacionario hacia $L_"ss" = (theta eta)\/(theta eta + 1 - eta) = 7\/9 approx 0.777778$; (iv) decaimiento armónico $Delta W_A^- = O(A^(-1))$ dominado en $A = 10^8$ por $beta^(126) = 0.02154$ en más de seis órdenes de magnitud; y (v) $A^2 S_A^"fix" (1) < A^2 S_A$ con razón decreciente de $1.01981$ a $1.00035$.

#v(0.3em)
#figure(
  table(
    columns: (0.65fr, 0.96fr, 0.96fr, 0.85fr, 0.90fr, 0.72fr, 0.72fr, 0.72fr, 0.62fr, 0.75fr),
    inset: 4.2pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 7.7pt)[$A$],
      text(fill: white, weight: "bold", size: 7.7pt)[$A^2 S_A^"fix" (1)$],
      text(fill: white, weight: "bold", size: 7.7pt)[$A^2 S_A$],
      text(fill: white, weight: "bold", size: 7.7pt)[Razón],
      text(fill: white, weight: "bold", size: 7.7pt)[$Delta_k$],
      text(fill: white, weight: "bold", size: 7.7pt)[$Delta W_A^(pi^+)$],
      text(fill: white, weight: "bold", size: 7.7pt)[$Delta W_A^+$],
      text(fill: white, weight: "bold", size: 7.7pt)[$R_"env"$],
      text(fill: white, weight: "bold", size: 7.7pt)[$T_"esc"$],
      text(fill: white, weight: "bold", size: 7.7pt)[$L_"ss"$],
    ),
    [$0.75$], [$0.000875$], [$0.000892$], [$1.01981$], [$0.000092$], [$8.357$], [$8.749$], [---], [$97$], [$0.7817$],
    [$1.50$], [$0.000867$], [$0.000877$], [$1.01079$], [$0.000077$], [$5.095$], [$5.292$], [---], [$106$], [$0.7803$],
    [$3.00$], [$0.000863$], [$0.000869$], [$1.00614$], [$0.000069$], [$3.133$], [$3.231$], [---], [$110$], [$0.7795$],
    [$10.0$], [$0.000858$], [$0.000861$], [$1.00275$], [$0.000061$], [$1.530$], [$1.566$], [---], [$113$], [$0.7786$],
    [$30.0$], [$0.000855$], [$0.000856$], [$1.00169$], [$0.000056$], [$0.999$], [$1.017$], [---], [$114$], [$0.7783$],
    [$100$], [$0.000851$], [$0.000852$], [$1.00122$], [$0.000052$], [$0.782$], [$0.794$], [$29.35$], [$116$], [$0.7780$],
    [$10^3$], [$0.000846$], [$0.000846$], [$1.00087$], [$0.000046$], [$0.664$], [$0.668$], [$27.84$], [$118$], [$0.7779$],
    [$10^6$], [$0.000835$], [$0.000836$], [$1.00048$], [$0.000036$], [$0.562$], [$0.562$], [$23.95$], [$123$], [$0.7778$],
    [$10^8$], [$0.000831$], [$0.000831$], [$1.00035$], [$0.000031$], [$0.513$], [$0.513$], [$22.36$], [$126$], [$0.7778$],
  ),
  caption: [Tabla 3: Verificación VFI en escala $log k$ hasta $A = 10^8$ (Teorema 2 y Observación 1). Aquí $Delta_k := A^2 S_A - 0.000800$ y $R_"env" := (S_A - S_A^"fix" (1)) \/ (S_A dot Delta_k dot Delta W_A^+)$ (reportada en el régimen asintótico $A >= 10^2$, descendiendo de $29.35$ a $22.36$); nótese $0 < Delta W_A^(pi^+) <= Delta W_A^+ -> 0^+$ y $L_"ss" -> 7\/9$.],
)

#figure(
  image("fig2_scaling_es.svg", width: 92%),
  caption: [Figura 1: (a) Convergencia uniforme de $A^2 S_A^"fix" (1)$ y $A^2 S_A$ hacia $(delta\/c_K)^2 = 0.000800$ (inserto: régimen de paciencia débil $beta = 0.90$ del Corolario 1). (b) Prueba analítica pura $beta^(T_M) g_(T_M) >> O(A^(-1))$, decaimiento de $Delta W_A^(pi^+) <= Delta W_A^+$ y límite estacionario $L_"ss" -> 7\/9$.],
)

// ============================================================================
// SECCIÓN 5: ARQUITECTURA CEGIS-LP Y CERTIFICACIÓN DETERMINISTA
// ============================================================================
= Arquitectura CEGIS-LP, Certificación Determinista y Escalabilidad

Para sintetizar barreras mucho más afiladas que las cotas afines cerradas, encadenar subregiones hasta la vecindad inmediata del punto de Skiba, transferir la metodología a tecnologías alternativas y escalar a cajas paramétricas anchas, formalizamos el motor general *_CEGIS-LP / log-PWL_*.

== Arquitectura Proposer--Verifier, Formulación LP y Auditoría sin `libm`

El diseño separa estrictamente la generación heurística/optimizadora de candidatos (_Proposer_) de su certificación matemática (_Verifier_), resumida visualmente en la Figura 2:

1. *Parametrización continua `log-PWL` con colas analíticas:* Sobre una malla estrictamente creciente de nodos $k_0 < k_1 < dots < k_n$ en coordenadas $z = log K$ ($z_i = log k_i$), toda función candidata $f : (0, oo) -> R$ (sea techo $Psi$, testigo $W$ o barrera de permanencia $B_theta$) queda unívocamente determinada por su vector de alturas nodales $y = (y_0, dots, y_n) in R^(n+1)$ y sus dos pendientes asintóticas analíticas $(s_"lo", D_"hi")$:
   $ f(K) = cases(
     y_0 + s_"lo" (log K - z_0) & "si " K <= k_0, \
     y_i + s_i (log K - z_i) & "si " K in [k_i, k_(i+1)] thin (s_i := (y_(i+1) - y_i)/(z_(i+1) - z_i)), \
     y_n + D_"hi" (log K - z_n) & "si " K >= k_n,
   ) $
   donde para los techos globales $Psi$ sobre $(0, oo)$ fijamos $s_"lo" = eta_- \/ (1 - beta_-)$ y $D_"hi" = eta_+ \/ (1 - beta_+)$, para los testigos $W$ sobre $[b, oo)$ empleamos la pendiente de cola sub-Bellman $s_"hi" <= eta_- \/ (1 - beta_-)$ ($s_"hi" = 0$ en la economía CES acotada y $s_"hi" > 0$ en el rayo homogéneo AK del Caso 4), y para barreras restringidas a $M = [b, h)$ fijamos $s_"lo" = D_"hi" = 0$ con $k_0 = b, k_n = h$.

2. *Formulación de Programación Lineal Dispersa (_Proposer_ HiGHS):* En cada ronda $r$, dado un conjunto finito de colocación activa $cal(C)_r = {(K_m, L_m, K'_m)}_(m=1)^(M_r)$ (formado por nodos, puntos medios, cuartos de intervalo y los peores contraejemplos acumulados de rondas previas), el _Proposer_ resuelve mediante HiGHS el programa lineal disperso en $(y, t) in R^(n+1) times R_(>= 0)^(n_"tv")$:
   $ min_(y, t) quad sum_(i=0)^n w_i y_i + lambda_"TV" sum_(j in cal(J)_"tv") t_j $
   sujeto a:
   - _Desigualdades de Bellman de peor caso_ sobre $(K_m, L_m, K'_m) in cal(C)_r$ (evaluando $f(K_m)$ y $f(K'_m)$ como combinaciones convexas lineales exactas de dos nodos adyacentes, con signo de $beta in {beta_-, beta_+}$ fijado por pase de referencia):
     $ f(K_m) >= u_"up" (c_m, L_m) + beta f(K'_m) + m_"slk" #h(8pt) ("para " Psi), #h(14pt) f(K_m) <= u_"worst" (c_m, L_m) + beta f(K'_m) - m_"slk" #h(8pt) ("para " W), $
     y análogamente sobre $cal(C)_r subset M^2$ para la barrera de permanencia $B_theta$ (con opción de maximizar directamente el margen mínimo $min_i (W(k_i) - y_i)$).
   - _Monotonicidad y cotas de derivada regional:_ $y_(i+1) - y_i >= m_("min", i) k_(i+1) (z_(i+1) - z_i)$ (garantizando $f'(K) >= m_("min", i)$, en particular $inf_(M_0) Psi' > (B^((0)))'$ y pendiente mínima en $M$).
   - _Regularización de variación total (TV) sobre #box[log-pendientes]:_ $t_j >= |s_(j+1) - s_j|$ para los nodos interiores $j in cal(J)_"tv"$.

3. *Auditoría continua Branch-and-Bound y residuales certificados $d_"ub,iv"$:* El $100\%$ de la validez matemática descansa sobre el _Verifier_. Este divide el dominio continuo en cajas 3D $(K, K', L)$ (o 1D en $K$ para $W$ y colas analíticas) mediante Branch-and-Bound con forma centrada y monotonía, exigiendo que toda hoja terminal satisfaga estrictamente en aritmética de intervalos de redondeo dirigido (núcleo nativo Rust vía `f64::next_down`/`next_up` e intervalos `Decimal` de $50$ dígitos en Python con logaritmo sin `libm` por reducción de rango de dos pasos; denotamos por $overline("iv")[dot.c]$ el extremo superior del recinto por intervalos):
   $ d_"ub,iv"^(B_theta) &:= sup_((K, K', L, theta_"par") in M^2 times [0,1) times cal(P)) overline("iv")[u(c, L) + beta B_theta (K') - B_theta (K)] <= 0, \
   d_"ub,iv"^Psi &:= sup_((K, K', L, theta_"par") in R_(>0)^2 times [0,1) times cal(P)) overline("iv")[u(c, L) + beta Psi(K') - Psi(K)] <= 0, \
   d_"ub,iv"^W &:= sup_((K, theta_"par") in [b, oo) times cal(P)) overline("iv")[W(K) - (u_"worst" (c_W (K), L_W (K)) + beta W(K'_W (K)))] <= 0, $
   junto con cotas continuas de derivada $< b$ y $< h$, y márgenes positivos de salidas adversas $E^+$ en $M, H_1, H_2$.

#v(0.2em)
#alg_box("1", "Bucle CEGIS-LP + Verificador Branch-and-Bound Continuo")[
  1. *Inicialización:* Fijar malla inicial log-espaciada $k_0 < dots < k_n$, colas analíticas $(s_"lo", D_"hi")$ (o $s_"hi"$ en testigos) y grilla de colocación inicial $cal(C)_0$.
  2. *Para ronda* $r = 1, dots, r_max$:
     - *(Proposer LP):* Resolver el LP disperso en HiGHS sobre $cal(C)_(r-1)$ con regularización TV y márgenes $m_"slk" > 0$, obteniendo las alturas nodales $y^((r))$ y el spline continuo `log-PWL` $f^((r))$.
     - *(Verifier B&B):* Auditar $f^((r))$ en todo el dominio continuo mediante B&B 3D/1D con forma centrada; si todas las hojas verifican $d_"ub,iv" <= 0$ en aritmética de intervalos con redondeo dirigido y pasan las auditorías de colas y derivadas, *retornar* el certificado $f^((r))$.
     - *(Refinamiento por contraejemplos):* Extraer las $N_"ce"$ peores cajas violadoras del árbol B&B, insertar sus puntos críticos en $cal(C)_r <- cal(C)_(r-1) union cal(E)_r$ (y opcionalmente nodos nuevos) y continuar a $r + 1$.
]

#v(0.2em)
#figure(
  image("fig_arch_es.svg", width: 98%),
  caption: [Figura 2: Arquitectura desacoplada _Proposer--Verifier_ del motor CEGIS-LP, frontera de la Base de Cómputo Confiable (TCB) y rama paralela de verificación formal en Lean 4.],
)

== Caso 1: Síntesis LP Determinista, Cadena No Estacionaria ($5 -> 4$) y Cascada Hasta $b_"ext" = 0.0030$

#thm_box("Proposición", "3", [Certificado determinista CEGIS-LP (Caso 1A) y descomposición no estacionaria (Caso 1C)])[
  Sea $(B_theta, Psi, W)$ la tripleta continua log-PWL sintetizada determinísticamente mediante HiGHS-LP sobre la caja completa $cal(P)$ ($B_theta$ de $57$ nodos —con versión compacta podada de $22$ nodos— sobre $M = [0.10, 0.28)$; $Psi$ de $193$ nodos con colas analíticas en $10^(-4)$ y $90$; $W$ de $74$ nodos sobre $[0.10, 5.5]$). Bajo auditoría B&B 3D/1D sin `libm` ($d_"ub,iv"^(B_theta) = -0.000200 <= 0$, $d_"ub,iv"^Psi = -0.000100 <= 0$, $d_"ub,iv"^W = -4.51 times 10^(-7) <= 0$, e $inf_(M_0) Psi' = 91.23 > 6.4234$):
  1. En los extremos de $M$, $B_theta (0.10) = -56.6905$ y $B_theta (0.28) = -52.3524$; frente al testigo $W_M$ y techo $Psi^sharp$, el margen en $M$ alcanza $19.0600$ (frente a techo $24.5153$) y el plazo cae a *$T_theta = 9$*. Acoplando $(Psi, W, B_theta)$, el margen sube a $21.0857$ (techo $24.2013$) y comprime el plazo certificado a *$T_"full" = 5$*.
  2. *Descomposición de la brecha ($5 -> 4 = tau_H^"VFI"$):* Sintetizando cadenas no estacionarias de horizonte finito $\{J_k\}_(k=0)^T$ se obtiene *$T_"ns" (cal(P)) = 5$* sobre la caja completa $cal(P)$ (holgura $+0.3055$) y *$T_"ns" (theta_0) = 4 = tau_H^"VFI"$* en el punto central $theta_0 = (0.75, 0.92, 0.97, 0.70)$ (holgura $+0.0942$). Así, el único período adicional ($5$ vs. $4$) proviene íntegramente de la incertidumbre paramétrica de la caja $cal(P)$, saturándose la cota en el punto central sin brecha estructural.
]

#cert_box(title: "Certificación y desigualdades verificadas (Caso 1A y 1C)")[
  Para el horizonte no estacionario del Caso 1C, definimos el operador de Bellman de permanencia de peor caso sobre funciones acotadas $J : M -> R$ mediante:
  $ (cal(T)_(cal(P))^+ J)(K) := sup_((K', L, theta_"par") in M times [0,1) times cal(P)) [ u(q K + F_A (K, L) - K', L) + beta J(K') ]. $
  El verificador B&B 3D audita por intervalos la cadena $J_0 >= Psi|_M$, $J_k >= cal(T)_(cal(P))^+ J_(k-1)$ ($k = 1, dots, T$), y certifica $inf_(K in M) [W(K) - J_T (K)] > 0$ (en $T = 5$ sobre $cal(P)$ y $T = 4$ sobre $\{theta_0\}$).
]

#v(0.2em)
#figure(
  table(
    columns: (1.5fr, 0.8fr, 0.9fr, 0.9fr, 1.1fr, 1.0fr),
    inset: 5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.3pt)[Configuración LP],
      text(fill: white, weight: "bold", size: 8.3pt)[Nodos $B_theta$],
      text(fill: white, weight: "bold", size: 8.3pt)[$T_theta$ ($W_M$)],
      text(fill: white, weight: "bold", size: 8.3pt)[$T_"full"$],
      text(fill: white, weight: "bold", size: 8.3pt)[$d_"ub,iv"^(B_theta)$],
      text(fill: white, weight: "bold", size: 8.3pt)[Síntesis (s)],
    ),
    [CEGIS-LP base (sin poda)], [$57$], [$9$], [$5$], [$-0.000200$], [$2.29$],
    [CEGIS-LP compacto (grilla podada)], [$22$], [$9$], [$5$], [$-0.000200$], [$0.95$],
  ),
  caption: [Tabla 4: Ablación de compacidad de la síntesis LP determinista en Caso 1A (HiGHS ralo reproducible sobre la caja completa $cal(P)$).],
)

Al reunir el Teorema 1 y la Proposición 3 obtenemos la cascada completa de afilamiento determinista sobre $M = [0.10, 0.28)$ ilustrada en la Figura 3:
- *Bloques de $2$ pasos ($B_0$):* $-38.144176 ==>$ *$tau_H <= 46$* (holgura $>= 2.564$).
- *Barrera afín cerrada de $1$ paso ($B_1$, Teorema 1):* $[-43.356, -43.047] ==>$ *$tau_H <= 23$* (holgura $7.776$).
- *Barrera adaptativa CEGIS-LP ($B_theta$, Proposición 3):* $[-56.6905, -52.3524] ==>$ *$T_theta = 9$* (frente a $W_M$, igualando el límite exacto de programación dinámica restringida $tau_H^"DP" = 9$) y *$T_"full" = 5$* con $(Psi, W, B_theta)$, cerrando en *$T_"ns" (theta_0) = 4 = tau_H^"VFI"$*.

#v(0.2em)
#figure(
  image("fig1_barrier_es.svg", width: 100%),
  caption: [Figura 3: (a) Comparación de las barreras analíticas ($B_0, B_1$) y CEGIS-LP determinista ($B_theta$, $57$ nodos; versión compacta $22$ nodos equivalente) frente a $W_M$ y $Psi^sharp$ sobre $M = [0.10, 0.28)$. (b) Cascada completa de plazos desde $tau_H <= 46$ hasta $T_"full" <= 5$ y $T_"ns" (theta_0) = 4 = tau_H^"VFI"$.],
)

Una limitación cuantitativa destacada en MR (2026) era la ausencia de un plazo explícito en el corredor comprendido entre el umbral de Skiba $S_A < 0.0025$ y $K_0 = 0.10$; la Proposición 1 redujo ese borde de $0.10$ a $0.05$. La siguiente proposición cierra casi íntegramente dicha brecha (Figura 4):

#thm_box("Proposición", "4", [Cascada continua CEGIS-LP casi hasta el umbral de Skiba ($b_"ext" = 0.0030$, Caso 1B)])[
  Consideremos el dominio ampliado $[b_"ext", 0.28)$ con $b_"ext" = 0.0030$ (cerrando el *$99.5\%$* de la brecha $[0.0025, 0.10)$ y el *$98.6\%$* del ancho $(S_A, 0.10)$ entre $S_A = 0.001588$ y $0.10$), particionado en $16$ subcajas ortogonales $(4_A times 4_beta)$ de $(A, beta)$ con consumo de salida en $[0.0030, 0.28)$ evaluado globalmente mediante $l_0 = 0.1695 > h\/2 = 0.14$. En cada una de las $16$ subcajas se certifican continuamente $(Psi, W)$, derivada $< b_"ext"$, salida adversa positiva por debajo de $b_"ext"$ (mínimo global $+0.1326$) y una cascada contigua de $5$ barreras de permanencia sobre las subregiones:
  $ [0.003, 0.006]_(T_1 <= 21), thin [0.006, 0.015]_(T_2 <= 13), thin [0.015, 0.040]_(T_3 <= 8), thin [0.040, 0.100]_(T_4 <= 5), thin [0.100, 0.280]_(T_5 <= 5). $
  En consecuencia, para toda condición inicial $K_0 in [0.0030, 0.28)$ y todo parámetro en $cal(P)$, el tiempo total máximo de escape hasta $H = [0.28, oo)$ queda certificado en a lo sumo *$T_"total" <= 21 + 13 + 8 + 5 + 5 = 52$* períodos.
]

#cert_box(title: [Certificación, partición en $(A, beta)$ y concatenación monótona (Caso 1B)])[
  Las $16$ subcajas se particionan exclusivamente en $(A, beta)$ ($4_A times 4_beta$) y no en $(q, eta)$ porque la posición del umbral de Skiba $S_A$ (que escala como $A^(-2)$) y la tasa de contracción temporal $beta^(T_i)$ dominan la sensibilidad del techo $Psi$ y de las barreras $B_i$ cerca de $b_"ext" = 0.0030$, mientras $(q, eta)$ mantienen un ancho relativo estrecho ($plus.minus 10^(-4)$). Como la ausencia certificada de salidas adversas por debajo de $b_"ext"$ implica $S_A < 0.0030$ en toda $cal(P)$, el estado estacionario productivo satisface uniformemente $K_"ss" (theta_"par") > 0.60$ sin estados estacionarios interiores en $[b_"ext", 0.28]$, y la supermodularidad del problema asegura la monotonicidad no decreciente de las políticas óptimas en $K$ (Dechert y Nishimura, 1983; Kamihigashi y Roy, 2007; MR, 2026), toda trayectoria óptima de escape en $(S_A, 0.60]$ obedece monotonicidad estricta $K_(t+1) > K_t$: una vez que la senda supera el borde derecho de la etapa $i$ hacia la etapa $i + 1$, no puede retroceder a la etapa $i$, permitiendo sumar directamente los tiempos máximos por etapa ($T_"total" <= sum_(i=1)^5 T_i = 52$).
]

#v(0.2em)
#figure(
  image("fig_nearskiba_es.svg", width: 96%),
  caption: [Figura 4: Mapa logarítmico del espacio de estados desde $S_A = 0.001588$ hasta $H_2 = [0.80, oo)$, mostrando las $5$ etapas encadenadas sobre $[0.0030, 0.28)$ con sus barreras escalonadas $B_(theta, i)$ frente a $W$ y $Psi$, cerrando el $99.5\%$ de la brecha hasta $S_A$.],
)

== Transferibilidad y Escalabilidad Determinista (Casos 4 y 6)

Para preservar la trazabilidad directa con los identificadores del archivo de certificados (`cegis_certificates.json.xz`) y el auditor independiente (`audit_standalone.py`), conservamos la numeración original `Casos 1–6`, agrupando aquí las pruebas deterministas (Casos 4 y 6) y en la Sección 6.3 las extensiones estocásticas (Casos 2, 3 y 5).

=== Caso 4: Transferibilidad al Régimen $A K$ Continuo por Tramos (Crecimiento Endógeno)

Como prueba concisa de transferibilidad hacia modelos de crecimiento endógeno sin ajuste manual de la arquitectura _CEGIS-LP_, consideramos una especificación lineal por tramos en la cual a partir de $h = 0.28$ los rendimientos marginales del capital dejan de ser decrecientes y la producción adopta un régimen asintótico lineal $F_"AK" (K, L) = (K\/h) F_A (h, L)$ para todo $K >= h$ (preservando la tecnología CES en $K < h$), con recursos totales $Y_"AK" (K, L) = q K + F_"AK" (K, L)$. Dado que el ingreso crece linealmente sin cota, el valor asintótico diverge logarítmicamente con pendiente límite exacta $D_"hi" = eta_+ \/ (1 - beta_+)$.

#thm_box("Proposición", "5", [Transferibilidad CEGIS-LP al régimen $A K$ continuo por tramos (Caso 4)])[
  Bajo la tecnología híbrida CES--AK sobre la caja paramétrica $cal(P)$, el par $(Psi_"AK", W_"AK")$ ($196$ y $74$ nodos) sintetizado mediante CEGIS-LP ralo satisface $d_"ub,iv"^Psi = -0.000100 <= 0$ (auditado por B&B 3D sobre $[10^(-4), 25.0]$ más colas analíticas), $d_"ub,iv"^W = -2.66 times 10^(-6) <= 0$ (auditado sobre $[0.10, 3.5]$ más rayo homogéneo exacto en $[3.5, oo)$ con residual $-0.000250 <= 0$), interioridad estricta del ocio $omega^*(oo) = 0.9913 < 1$, e inexistencia de salidas adversas en todo $[0.28, oo)$:
  1. *Valores críticos en $h = 0.28$:* $Psi_"AK" (0.28) = +243.4645$ y $W_"AK" (0.28) = +238.1434$ (con $W_"AK" (0.10) = +209.7896$).
  2. *Plazo de escape comprimido:* Acotando con $B_theta$ y el par $(Psi_"AK", W_"AK")$, el tiempo máximo de tránsito en $M$ cae a *$T_"AK" = 4$* períodos ($inf_M (W - B_theta) = +266.1664$, $sup_M (Psi_"AK" - B_theta) = +295.9307$).
  3. *Auditoría completa de salidas adversas:* Mediante B&B 1D sobre $M$ y $[0.28, 3.5]$ más el rayo homogéneo analítico en $[3.5, oo)$ se certifican $m_(M,"iv") = +3.6786$, $m_(H_1,[0.28,3.5],"iv") = +3.5193$ y $m_(H_2,[3.5,oo),"iv") = +59.7121$, junto con holguras de derivada $< b$ de $+295.08$ y $< h$ de $+82.01$.
]

#cert_box(title: [Reducción exacta del rayo homogéneo en la cola AK $[3.5, oo)$])[
  Para todo $K = lambda k_"tail"$ con $k_"tail" = 3.5$ y $lambda >= 1$, el escalado proporcional de política $(K, K', L) |-> (lambda k_"tail", lambda k'_"tail", L_"tail")$ preserva la factibilidad y escala linealmente el consumo como $c(lambda) = lambda c_"tail"$ porque $Y_"AK" (lambda k_"tail", L_"tail") = lambda Y_"AK" (k_"tail", L_"tail")$. Con $k'_"tail" = 5.6830 > 3.5$, tanto $K$ como $K'$ caen en la cola logarítmica $W_"AK" (x) = W_"AK" (k_"tail") + s_"hi" log(x\/k_"tail")$; así la desigualdad sub-Bellman $W_"AK" (lambda k_"tail") <= u_"worst" (lambda c_"tail", L_"tail") + beta W_"AK" (lambda k'_"tail")$ se reduce a verificar el punto base $k_"tail" = 3.5$ (donde $W_"AK" (k'_"tail") > 0$ y el residual en `Decimal` de $50$ dígitos vale $-0.000250 <= 0$) junto con la condición de pendiente $(1 - beta_-) s_"hi" <= eta_-$, garantizando $d\/d(log lambda) [W_"AK" - u - beta W_"AK"] <= 0$ para todo $lambda >= 1$.
]

=== Caso 6: Pruebas de Estrés en Cajas Paramétricas Anchas (Hasta $10 times$)

La caja de referencia $cal(P)$ posee un radio estrecho ($plus.minus 0.001$ en $A$, $plus.minus 0.0001$ en $beta, q, eta$). Para demostrar que el motor CEGIS-LP es un método general y no sobreajustado a un entorno puntual, ejecutamos pruebas de estrés en dos familias paramétricas ampliadas hasta $10 times$ su ancho en tasas e incertidumbre macroeconómica de $plus.minus 1.33\%$ en productividad: `MR_Box_7_1` ($A in [0.749, 0.751]$, $beta in [0.969, 0.971]$, $q in [0.919, 0.921]$, $eta in [0.699, 0.701]$) y `Macro_10x_Box` ($A in [0.740, 0.760]$, $beta in [0.969, 0.971]$, $q in [0.919, 0.921]$, $eta in [0.699, 0.701]$).

#thm_box("Proposición", "6", [Escalabilidad certificada de CEGIS-LP en cajas paramétricas anchas (Caso 6)])[
  Particionando `MR_Box_7_1` en $8$ subcajas ($2_beta times 2_q times 2_eta$) y `Macro_10x_Box` en $128$ subcajas ($16_A times 2_beta times 2_q times 2_eta$), CEGIS-LP sintetiza y re-audita por intervalos de manera completa en todas las subcajas una tripleta $(Psi, W, B_theta)$ satisfaciendo salidas adversas positivas en $M, H_1, H_2$, derivadas $< b \/ < h$, y plazo uniforme comprimido *$T_"full" = 6$* períodos (Tabla 5).
]

#v(0.2em)
#figure(
  table(
    columns: (1.18fr, 0.78fr, 1.32fr, 0.54fr, 0.76fr, 0.74fr, 0.74fr, 0.72fr, 0.80fr),
    inset: 4.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.0pt)[Caja],
      text(fill: white, weight: "bold", size: 8.0pt)[#box[Subcajas]],
      text(fill: white, weight: "bold", size: 8.0pt)[Rango $(A; beta, q, eta)$],
      text(fill: white, weight: "bold", size: 8.0pt)[$T_"full"$],
      text(fill: white, weight: "bold", size: 8.0pt)[Sal. $M$],
      text(fill: white, weight: "bold", size: 8.0pt)[Sal. $H_1$],
      text(fill: white, weight: "bold", size: 8.0pt)[Sal. $H_2$],
      text(fill: white, weight: "bold", size: 8.0pt)[Síntesis],
      text(fill: white, weight: "bold", size: 8.0pt)[Re-verif.],
    ),
    [`MR_Box_7_1`], [$8$], [$[0.749, 0.751]$; $10 times$ tasas], [*$6$*], [$+0.5850$], [$+0.042$], [$+2.563$], [$29.9$ s], [$10.66$ s],
    [`Macro_10x_Box`], [$128$], [$[0.740, 0.760]$; $10 times$ tasas], [*$6$*], [$+0.5569$], [$+0.028$], [$+2.545$], [$745.7$ s], [$160.21$ s],
  ),
  caption: [Tabla 5: Prueba de estrés CEGIS-LP en cajas anchas (Caso 6). La columna Re-verif. reporta el tiempo medido del auditor independiente `audit_standalone.py`.],
)

// ============================================================================
// SECCIÓN 6: TEORÍA CONVERSO-ESTOCÁSTICA DE DOOB Y SUPERVIVENCIA BAJO CHOQUES
// ============================================================================
= Teoría Converso-Estocástica de Doob y Supervivencia bajo Choques

== Lema 2, Corolario 2 y Teorema 3 (Completitud Estocástica de Doob)

Para certificar probabilidades de supervivencia cuando la economía enfrenta choques agregados de ruina o regímenes persistentes de recesión, desarrollamos primero la herramienta de supermartingala detenida y su teorema converso bajo compacidad.

#thm_box("Lema", "2", [Supermartingala detenida y parada opcional de Doob])[
  Sea $(omega_t)_(t >= 0)$ un proceso de choques macroeconómicos Markovianos sobre $(Omega, cal(F), Pr)$ bajo la condición de integrabilidad $sup_(t <= T) E[ |V(K_(t and tau), omega_(t and tau))| ] < oo$ para todo horizonte finito $T >= 1$. Sea $B : [b, oo) times Omega -> R$ una función medible y acotada en $[b, oo)$ que satisface la desigualdad de Bellman en un paso para toda acción de permanencia en $M = [b, h)$ y toda acción de salida ascendente hacia $H = [h, oo)$:
  $ B(K, omega) >= u(c, L) + beta E[B(K', omega') | K, omega, a] #h(12pt) (K in M, thin K' >= b). $
  Considérese cualquier política con ausencia de salida inferior c.s. ($K_tau >= b$ casi seguramente en el tiempo de parada $tau = inf{t >= 0 : K_t in.not M}$) y tal que $E[sum_(j=0)^((t and tau) - 1) beta^j |u_j| ] < oo$. Entonces el proceso detenido $Z_(t and tau) := beta^(t and tau) B(K_(t and tau), omega_(t and tau)) + sum_(j=0)^((t and tau) - 1) beta^j u_j$ es una _supermartingala_ integrable respecto de la filtración natural $cal(F)_t$, y para todo horizonte finito $T >= 1$ se cumple la cota de parada opcional:
  $ E_(x_0, omega_0)[J(pi)] <= B(x_0, omega_0) + E_(x_0, omega_0)[beta^(T and tau)(V(K_(T and tau), omega_(T and tau)) - B(K_(T and tau), omega_(T and tau)))]. $
]

#proof_block(title: "Demostración del Lema 2")[
  Bajo la desigualdad de Bellman esperada extendida sobre $M times [b, oo)$, la condición de no salida inferior $K_tau >= b$ c.s. asegura que $K_((t+1) and tau)$ permanece en el dominio $[b, oo)$ de $B$. Por integrabilidad, la diferencia condicional satisface:
  $ E[Z_((t+1) and tau) - Z_(t and tau) | cal(F)_t] = bold(1)_({tau > t}) beta^t {u_t + beta E[B(K_(t+1), omega_(t+1)) | cal(F)_t] - B(K_t, omega_t)} <= 0, $
  por lo que $(Z_(t and tau))$ es una $cal(F)_t$-supermartingala integrable. Aplicando el Teorema de Parada Opcional de Doob en el tiempo acotado $T and tau$ se sigue $E[Z_(T and tau)] <= Z_0 = B(x_0, omega_0)$; sustituyendo el valor de continuación futuro en $T and tau$ por $V(K_(T and tau), omega_(T and tau))$ (por optimalidad de Bellman) se obtiene directamente la cota esperada del enunciado.
]

#thm_box("Corolario", "2", [Reducción a ruina, probabilidad de supervivencia y tiempo medio de salida])[
  Bajo los supuestos del Lema 2:
  1. *(Reducción con valor absorbente de ruina $U_0$):* Si en cada período ocurre transición irreversible hacia un estado absorbente de valor $U_0$ con probabilidad $p in [0, 1)$, la normalización $tilde(V) = V - (beta p U_0)\/(1 - tilde(beta)_p)$ y $tilde(B) = B - (beta p U_0)\/(1 - tilde(beta)_p)$ cancela idénticamente el término de salto $beta p U_0$, reduciendo el problema con valor terminal $U_0$ a la ecuación de Bellman con descuento efectivo $tilde(beta)_p = beta (1 - p)$ y recompensas $u$ exactamente inalteradas. Si una política satisface $J_(x_0) (pi; tilde(beta)_p) > B(x_0) + tilde(beta)_p^T sup_(x in M) [Psi(x) - B(x)]$ en ausencia de quiebra durante $T = T^*(p)$ períodos, entonces todo óptimo sobrevive la transición antes de $T^*(p)$ con probabilidad al menos $Pr(tau_H < oo | K_0 = b, G) >= (1 - p)^(T^*(p))$.
  2. *(Brecha de Doob $epsilon.alt_0$ y finitud de $E[tau]$ en Markov):* Sea $y_"max" = q_+ h + F_(A_+) (h, 1)$ la cota máxima de capital en un salto ascendente desde $M$, y defínanse $m_inf := min_(omega in {G, B}) inf_(K in M) [W_omega (K) - B_omega (K)]$, $d_"stay" := max_(omega') sup_(K in M) [Psi_(omega') (K) - B_(omega') (K)]$ y $d_"exit" := max_(omega') sup_(y in [h, y_"max"]) [Psi_(omega') (y) - B_(omega') (y)]$ (bajo extensión constante $B_(omega') (y) = B_(omega') (h)$ en $[h, y_"max"]$ con $Psi_(omega')$ creciente, $d_"exit" = max_(omega') [Psi_(omega') (y_"max") - B_(omega') (h)]$). Si existe $T_0 >= 1$ tal que
     $ epsilon.alt_0 := (m_inf - beta_+^(T_0) d_"stay") / (beta_0^1 d_"exit" - beta_+^(T_0) d_"stay") > 0 #h(10pt) ("con " beta_0^1 = 1 "o" beta_0^1 = beta_+ "si " tau >= 1), $
     entonces cualquier óptimo con ausencia de salida inferior c.s. verifica $Pr(tau <= T_0 | K_0 in M, omega_0) >= epsilon.alt_0$ uniformemente sobre $M times {G, B}$, por lo que $Pr(tau > k T_0) <= (1 - epsilon.alt_0)^k -> 0$, $Pr(tau = oo) = 0$ y $E[tau] <= T_0 \/ epsilon.alt_0 < oo$.
]

#proof_block(title: "Demostración del Corolario 2")[
  Para la parte (1), obsérvese que, condicionada a no sufrir ruina previa, la evolución del capital bajo una política óptima estacionaria es determinista. Tras cancelar la constante de ruina $(beta p U_0)\/(1 - tilde(beta)_p)$, si esa trayectoria condicional permaneciera en $M$ durante $T^*(p)$ períodos recibiría a lo sumo $B(x_0) + tilde(beta)_p^(T^*(p)) sup_M (Psi - B) < W(x_0) <= V(x_0; tilde(beta)_p)$, contradiciendo la optimalidad. En consecuencia, toda senda óptima desde $K_0 in M$ debe haber cruzado $h$ o haberse topado con ruina antes de $T^*(p)$; como el evento de no quiebra durante $0 <= t < T^*(p)$ tiene probabilidad $(1 - p)^(T^*(p))$, resulta $Pr(tau_H < oo | K_0 = b, G) >= (1 - p)^(T^*(p))$. Para la parte (2), partiendo de cualquier $(K_0, omega_0) in M times {G, B}$, el Lema 2 en $T = T_0$ acota $W_(omega_0) (K_0) <= E[J(pi)] <= B_(omega_0) (K_0) + Pr(tau <= T_0) beta_0^1 d_"exit" + (1 - Pr(tau <= T_0)) beta_+^(T_0) d_"stay"$ (donde $tau >= 1$ en $K_0 in M$ y $K_tau in [h, y_"max"]$ cuando $tau <= T_0$, y $K_(T_0) in M$ cuando $tau > T_0$). Reordenando y acotando $W_(omega_0) (K_0) - B_(omega_0) (K_0) >= m_inf$ uniformemente en $M times {G, B}$ rinde exactamente $Pr(tau <= T_0 | K_0 in M, omega_0) >= epsilon.alt_0 > 0$. Aplicando iterativamente la propiedad fuerte de Markov en múltiplos $k T_0$ ($k >= 1$), la probabilidad de permanecer sin salir en $k$ bloques consecutivos cumple $Pr(tau > k T_0) <= (1 - epsilon.alt_0)^k -> 0$, garantizando $Pr(tau = oo) = 0$ y $E[tau] <= T_0 sum_(k=0)^oo (1 - epsilon.alt_0)^k = T_0 \/ epsilon.alt_0 < oo$.
]

El siguiente teorema eleva el Lema 2 a un criterio de completitud general en control óptimo estocástico bajo compacidad (análogo estocástico del Teorema 7 de MR):

#thm_box("Teorema", "3", [Completitud estocástica: converso para FPBB estocásticas de Doob])[
  Considérese un proceso de decisión Markoviano compacto bajo tres hipótesis estructurales: **(A1)** espacio de estados compacto $cal(X) = [b, K_"max"] times Omega$ ($Omega$ finito, $beta in (0, 1)$, $y_"max" <= K_"max"$), correspondencia factible continua y compacta, y ausencia de salida inferior c.s. ($K_(t+1) >= b$) desde $cal(X)_M = [b, h) times Omega$; **(A2)** retorno $u$ continuo, monótono creciente en consumo y uniformemente acotado sobre el conjunto factible compacto; y **(A3)** funciones valor continuas del problema libre $V$ y del problema restringido al cierre $[b, h]$,
  $ V_M^"stay" (K, omega) := sup{E_(K, omega) [sum_(t=0)^oo beta^t u(c_t, L_t)] : K_t in [b, h] thin forall t >= 0}, $
  satisfaciendo la brecha de borde $V(h, omega) > V_M^"stay" (h, omega)$ para todo $omega in Omega$. Son equivalentes:
  1. *(Escape uniforme de Doob):* Existe $C < oo$ tal que todo óptimo markoviano estacionario $pi^*$ satisface $sup_(x in cal(X)_M) E_x^(pi^*) [tau_H] <= C$ (equiv., existen $T_0 >= 1$ y $epsilon.alt_0 > 0$ con $inf_(x in cal(X)_M) Pr_x^(pi^*) (tau_H <= T_0) >= epsilon.alt_0$, implicando escape casi seguro $Pr_x^(pi^*) (tau_H < oo) = 1$).
  2. *(Brecha estricta de valor):* $delta_0 := inf_(x in cal(X)_M) [V(x) - V_M^"stay" (x)] > 0$.
  3. *(Existencia de FPBB estocástica estricta de Doob):* Existe una tripleta acotada $(Psi, W, B)$ (e incluso una tripleta continua `log-PWL` con un número finito de nodos) que satisface las desigualdades de súper-barrera, testigo y permanencia extendida del Lema 2 junto con $inf_(cal(X)_M) (W - B) > 0$ y brecha uniforme de Doob $epsilon.alt_0 > 0$ en el Corolario 2.
]

#obs_box("2", [Aplicación al entorno CES--log con utilidad no acotada en la frontera])[
  En la economía CES--log, las acciones factibles degeneradas de borde ($c = 0$ o $L = 1$) producen $u = -oo$. Sin embargo, la interioridad uniforme de las acciones óptimas $(c_t, 1 - L_t)$ garantiza que todos los óptimos residen en un subconjunto compacto interior donde $u$ es continuo y acotado, cumpliéndose **(A2)** sobre dicho compacto, mientras que en las acciones de borde con $u = -oo$ las desigualdades súper-Bellman se verifican automáticamente.
]

#proof_block(title: "Demostración del Teorema 3")[
  *(3) $=>$ (1):* Sigue inmediatamente del Corolario 2 (parte 2), obteniendo $inf_(cal(X)_M) Pr_x (tau_H <= T_0) >= epsilon.alt_0 > 0$ y $sup_(cal(X)_M) E_x [tau_H] <= T_0 \/ epsilon.alt_0 < oo$. Inversamente, bajo (1), fijando $T_0 := ceil(2 C)$ la desigualdad de Markov rinde $Pr_x^(pi^*) (tau_H > T_0) <= C \/ T_0 <= 1\/2$, dando $inf_(cal(X)_M) Pr_x^(pi^*) (tau_H <= T_0) >= 1\/2 > 0$. \
  *(1) $=>$ (2):* Supóngase por contradicción que $delta_0 = inf_(cal(X)_M) (V - V_M^"stay") = 0$. Como $V$ y $V_M^"stay"$ son continuas sobre el compacto $[b, h] times Omega$, el conjunto cerrado $E_0 := {x in [b, h] times Omega : V(x) = V_M^"stay" (x)}$ es no vacío y, dado $V(h, omega) > V_M^"stay" (h, omega)$ por hipótesis, satisface $E_0 subset cal(X)_M$. Por el teorema de existencia de selectores medibles estacionarios óptimos bajo compacidad y continuidad (Hernández-Lerma y Lasserre, 1996, Teorema 4.2.3), existen políticas estacionarias markovianas óptimas tanto para el problema restringido $V_M^"stay"$ como para el problema libre $V$. En particular, sea $tilde(pi)$ una política estacionaria markoviana óptima para $V_M^"stay"$ en $[b, h] times Omega$; esta mantiene $K_t in [b, h]$ para todo $t >= 0$ y alcanza $V_M^"stay" (x) = V(x)$ sobre todo $x in E_0$, dejando al cerrado $E_0$ invariante (cualquier transición con probabilidad positiva desde $x in E_0$ hacia $y$ con $V(y) > V_M^"stay" (y)$ violaría $E[V(X_1) - V_M^"stay" (X_1) | x, tilde(pi)(x)] = 0$ y por ende $V(x) = V_M^"stay" (x)$). Pegando $tilde(pi)$ sobre el cerrado invariante $E_0$ con una política estacionaria markoviana óptima libre fuera de $E_0$ se construye una política estacionaria markoviana óptima global $pi^*$ que en cualquier $x_0 in E_0 subset cal(X)_M$ verifica $Pr_(x_0)^(pi^*) (tau_H = oo) = 1$, contradiciendo (1). \
  *(2) $=>$ (3):* Extendiéndose $V_M^"stay"$ sobre $[b, y_"max"] times Omega$ mediante la truncación $B(K, omega) := V_M^"stay" (min{K, h}, omega)$, verificamos la desigualdad extendida del Lema 2: si la acción cae en $K' in [b, h)$, vale $u + beta E[B(K', omega')] = u + beta E[V_M^"stay" (K', omega')] <= V_M^"stay" (K, omega) = B(K, omega)$; si sale hacia $K' in [h, y_"max"]$, al reemplazar $K'$ por $h$ el consumo sube estrictamente a $c(h) = q K + F_A (K, L) - h > c(K') > 0$ (preservando la factibilidad interior) mientras $B(K', omega') = V_M^"stay" (h, omega')$ permanece constante, de modo que por monotonía $u(c(K'), L) + beta E[B(K', omega')] <= u(c(h), L) + beta E[V_M^"stay" (h, omega')] <= V_M^"stay" (K, omega) = B(K, omega)$. Tomando $Psi = V$ y $W = V$ (o cualquier aproximación continua `log-PWL` $(B_"pwl", W_"pwl", Psi_"pwl")$ a distancia uniforme $epsilon.alt < (1 - beta) delta_0 \/ 16$ respecto de $(B, V, V)$, definiendo $tilde(B) := B_"pwl" + ((1 + beta)\/(1 - beta)) epsilon.alt$, $tilde(Psi) := Psi_"pwl" + ((1 + beta)\/(1 - beta)) epsilon.alt$ y $tilde(W) := W_"pwl" - ((1 + beta)\/(1 - beta)) epsilon.alt$, garantizando ambas desigualdades con $inf_(cal(X)_M) (tilde(W) - tilde(B)) >= delta_0 - (4\/(1 - beta)) epsilon.alt > (3\/4) delta_0 > 0$), basta elegir $T_0$ suficientemente grande para que $beta^(T_0) sup(tilde(Psi) - tilde(B)) <= delta_0 \/ 2$ y que el denominador satisfaga $beta_0^1 d_"exit" - beta^(T_0) d_"stay" > 0$ (garantizado porque $d_"exit" >= min_(omega) (tilde(Psi)(h, omega) - tilde(B)(h, omega)) > 0$ gracias a la brecha de borde $V(h, omega) > V_M^"stay" (h, omega)$ en **(A3)**), asegurando $epsilon.alt_0 > 0$.
]

_Contraste con la literatura de Lyapunov estocástico:_ En control estocástico y teoría de cadenas de Markov existen teoremas conversos clásicos tipo Foster--Lyapunov (Kushner, 1967; Meyn y Tweedie, 2009) y certificados de barrera estocástica para sistemas dinámicos cerrados (Prajna et al., 2007); sin embargo, dichos resultados caracterizan la recurrencia o finitud de tiempos de llegada bajo una *dinámica exógena o política de retroalimentación fija*. La novedad específica del Teorema 3 radica en acoplar directamente la super-barrera de supermartingala a la *selección endógena de políticas óptimas mediante la brecha de funciones valor* $inf_(cal(X)_M)(V - V_M^"stay") > 0$, certificando simultáneamente a *toda* política estacionaria óptima $pi^*$ sin exigir conocimiento explícito de $pi^*$.

== Dicotomía Económica en VFI Estocástica (Tabla 6)

Antes de construir los certificados continuos CEGIS-LP, resolvemos el equilibrio exacto mediante VFI estocástica continua por sección áurea bajo dos regímenes de incertidumbre (Tabla 6 y Figura 5a), revelando una dicotomía económica estructural entre choques irreversibles y choques recuperables:

- *Colapso de inversión bajo riesgo de ruina irreversible exógena:* Un incremento en $p in [0\%, 8.0\%]$ reduce directamente el factor de descuento efectivo $tilde(beta)_p = beta(1 - p)$. Al penalizar el valor presente del futuro, se desincentiva la acumulación: la inversión cae ($K'(0.10)$ desciende de $0.13364$ a $0.12757$), el esfuerzo laboral se contrae ($L$ cae de $0.6626$ a $0.6008$) y la trampa de pobreza se expande casi al triple ($S^"ruin" (p)$ sube de $0.001588$ en $p=0\%$ a $0.002013$ en $p=2\%$ y $0.004589$ en $p=8\%$, un salto de $2.89 times$).
- *«Huida hacia la seguridad» precautoria bajo recesión recuperable de Markov ($p_"rec" = 1\/3$):* Cuando la crisis es una fase recesiva transitoria ($A_B = 0.35 < A_G = 0.75$) con tasa de recuperación positiva, el umbral crítico apenas aumenta ($S_G$ pasa de $0.001588$ a $0.001774$, $+11.7\%$ en $p=8\%$, con $K_B^*$ bajando de $0.01086$ a $0.00991$). Crucialmente, en el estado próspero $G$ la política óptima invierte la respuesta anterior: tanto la inversión ($K'_G (0.10)$ sube de $0.13364$ a $0.13475$) como el trabajo ($L_G$ sube de $0.6626$ a $0.6759$) aumentan precautoriamente para acumular capital y alejarse de la vecindad del abismo antes de sufrir la recesión. En el Apéndice A.4 documentamos cómo este efecto se intensifica cuanto más persistente es la recesión ($p_"rec" = 0.50 -> 0.20$). Como veremos en el Caso 5, esta misma lógica precautoria se magnifica al volver endógena la probabilidad de ruina $p(K) = p bold(1)_(K < 0.28)$.

#figure(
  table(
    columns: (0.7fr, 1.0fr, 0.9fr, 0.85fr, 1.0fr, 1.0fr, 0.9fr, 0.85fr),
    inset: 5.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.3pt)[$p$],
      text(fill: white, weight: "bold", size: 8.3pt)[$S^"ruin"$],
      text(fill: white, weight: "bold", size: 8.3pt)[$K'_"ruin"$],
      text(fill: white, weight: "bold", size: 8.3pt)[$L_"ruin"$],
      text(fill: white, weight: "bold", size: 8.3pt)[$S_G^"Markov"$],
      text(fill: white, weight: "bold", size: 8.3pt)[$K_B^*$],
      text(fill: white, weight: "bold", size: 8.3pt)[$K'_G (0.10)$],
      text(fill: white, weight: "bold", size: 8.3pt)[$L_G$],
    ),
    [$0.0\%$], [$0.001588$], [$0.13364$], [$0.6626$], [$0.001588$], [$0.01086$], [$0.13364$], [$0.6626$],
    [$0.5\%$], [$0.001670$], [$0.13324$], [$0.6579$], [$0.001603$], [$0.01062$], [$0.13373$], [$0.6638$],
    [$1.0\%$], [$0.001769$], [$0.13294$], [$0.6545$], [$0.001608$], [$0.01062$], [$0.13379$], [$0.6645$],
    [$1.5\%$], [$0.001884$], [$0.13254$], [$0.6502$], [$0.001622$], [$0.01062$], [$0.13386$], [$0.6654$],
    [$2.0\%$], [$0.002013$], [$0.13219$], [$0.6464$], [$0.001636$], [$0.01062$], [$0.13392$], [$0.6660$],
    [$5.0\%$], [$0.003053$], [$0.12990$], [$0.6225$], [$0.001703$], [$0.01038$], [$0.13435$], [$0.6710$],
    [$8.0\%$], [$0.004589$], [$0.12757$], [$0.6008$], [$0.001774$], [$0.00991$], [$0.13475$], [$0.6759$],
  ),
  caption: [Tabla 6: Dicotomía en VFI estocástica continua: colapso bajo ruina exógena absorbente frente a «huida hacia la seguridad» en recesión recuperable de Markov ($p_"rec" = 1\/3$).],
)

== Certificación Estocástica: Casos 2, 3 y 5

=== Caso 2: Bandas Continuas de Ruina Exógena sobre $p in [0\%, 2.0\%]$

#thm_box("Proposición", "7", [Certificado continuo en $60$ bandas de riesgo de ruina $p in [0\%, 2.0\%]$ (Caso 2)])[
  Consideremos la partición continua y contigua en $60$ sub-bandas del factor de descuento efectivo $tilde(beta)_p = beta (1 - p) in [0.950502, 0.9701]$, que recubre sin huecos todo $(beta, p) in [0.9699, 0.9701] times [0, 0.02]$. En cada una de las $60$ bandas $j = 0, dots, 59$, el motor CEGIS-LP certifica una tripleta $(Psi_j, W_j, B_("cegis", j))$ con $d_"ub,raw" <= 0$ sin desplazamientos aditivos, auditoría 3D de intervalos $d_"ub,iv" <= -0.000100$, monotonicidad en $M$ ($min W'_j >= m_G$), cotas de derivadas $< b$ y $< h$, y márgenes de salida adversa positivos en $M$, $H_1$ y $H_2 = [0.80, oo)$. Por el Corolario 2 (parte 1):
  1. En la banda superior ($p approx 0\%$, $tilde(beta)_p in [0.969732, 0.9701]$): el margen sobre $B_1$ es $+7.575$ con salidas adversas $M \/ H_1 \/ H_2 = +0.781$ / $+0.225$ / $+2.730$, plazo $T^*_(B_1) = 22$ y plazo comprimido $T^*_"CEGIS" = 6$.
  2. En todo el rectángulo extremo de riesgo $p = 2.0\%$ ($tilde(beta)_p in [0.950502, 0.950698]$, cubierto por las bandas $j = 0, dots, 5$), se certifica margen positivo sobre $B_1$ ($>= +0.0579$ en la esquina $j = 0$, con $T^*_(B_1) (2.0\%) = 93$, supervivencia $(0.98)^93 >= 15.27\%$, exacto $0.152762$) y plazo comprimido uniforme *$T^*_"CEGIS" in {5, 6}$* en las $60$ bandas ($T^*_"CEGIS" (2.0\%) = 5$ en la esquina inferior, elevando la supervivencia de Doob garantizada a *$(0.98)^5 >= 90.39\%$*, exacto $0.903921$, redondeada estrictamente hacia abajo; Figura 5b).
]

_Invariancia respecto a $V_"ruin"$:_ Como en el Caso 2 el riesgo de ruina exógeno $p$ es independiente de $(K', L)$, la función valor bajo cualquier valor terminal finito $V_"ruin"$ satisface $V(K; V_"ruin") = V(K; 0) + (beta p V_"ruin")\/(1 - tilde(beta)_p)$, por lo que tanto la política óptima $(K'_t, L_t)$ como el umbral $S^"ruin" (p)$ y las cotas de supervivencia $(1-p)^(T^*)$ son exactamente invariantes a $V_"ruin"$, incluso cuando $V(K) < 0 = V_"ruin"$. En la esquina $j = 0$ ($p = 2.0\%$), resulta $T^*_"CEGIS" (2.0\%) = 5$ debido al menor ancho sub-banda de $tilde(beta)_p$ y a la mayor contracción $(0.9505)^T$.

#figure(
  image("fig3_stochastic_es.svg", width: 92%),
  caption: [Figura 5: (a) Dicotomía VFI estocástica: colapso de inversión bajo ruina exógena frente a «huida hacia la seguridad» en recesión de Markov ($p_"rec" = 1\/3$) y ruina endógena $p(K) = p bold(1)_(K < 0.28)$ (Caso 5). (b) Probabilidad certificada de supervivencia $(1-p)^(T^*(p))$ en las $60$ bandas continuas de $tilde(beta)_p$.],
)

=== Caso 3: Sistema Acoplado de Markov $(G, B)$, Compresión $(B_(G, theta), B_(B, theta))$ y $1 thin 054$ Hojas en $H_(1,B)$

#thm_box("Proposición", "8", [Supervivencia casi segura y compresión de tiempo medio esperado en Markov $(G, B)$ (Caso 3)])[
  Para el sistema acoplado de dos estados $(G, B)$ con transición adversa $p in {0\%, 0.5\%, 1.0\%, 1.5\%, 2.0\%, 5.0\%, 8.0\%, 12.0\%}$ y recuperación $p_"rec" = 1\/3$ sobre $tilde(cal(P))$, el motor CEGIS-LP acoplado certifica en las $64$ bandas externas de $(beta, p)$ y en las $32$ subcajas 4D ortogonales de $(A_G, A_B, q, eta)$ ($4_(A_G) times 2_(A_B) times 2_q times 2_eta$, auditada cada hoja mediante B&B 3D en $(K, K', L)$, desplegando en total *$1 thin 054$ hojas continuas* $(b, s)$ exportadas y re-auditadas independientemente):
  1. Márgenes afines de permanencia positivos ($"marg"_G >= 4.45$, $"marg"_B >= 0.84$, $T^*_G <= 34$, $T^*_B <= 88$), derivadas $< b$ y $< h$ en ambos estados, salidas adversas positivas en $M$ ($G >= +1.07$, $B >= +0.002$), $H_(1,G) >= +0.47$, $H_2 >= +3.02$, y salida adversa positiva en las $1 thin 054$ hojas continuas de $H_(1,B)$ ($m_(H_1,B,"32bx") >= +0.00015 > 0$).
  2. *Compresión acoplada CEGIS-LP de $(B_(G, theta), B_(B, theta))$ y comparación frente a $E_"VFI" [tau]$:* Mientras la barrera afín analítica arrojaba cotas conservadoras de Doob de miles de períodos ($E[tau] <= 1 thin 480.3$ en $p=0\%$ y $13 thin 322.8$ en $p=12\%$), la síntesis conjunta de una pareja acoplada $(B_(G, theta), B_(B, theta))$ reduce los plazos de transición por estado a $(T^*_G, T^*_B) = (5, 5)$ (y $(6, 6)$ en $p = 12\%$), multiplica la brecha de Doob en más de un orden de magnitud (*$epsilon.alt_0^"comp" in [0.3869, 0.4088]$* con $T_0^"opt" in {14, 15}$), y desploma la cota superior garantizada sobre el tiempo esperado de escape hasta *$E[tau] <= 35.1"–"38.8$ períodos* (compresión de $42 times$ a $343 times$; Teorema 3 y Corolario 2). En el punto central $theta_0$, el óptimo verdadero de malla VFI exhibe $max_(M times {G, B}) E_"VFI" [tau] in [5.81, 5.92]$ períodos (alcanzado desde el estado recesivo $B$ con $p_"rec" = 1\/3$; Tabla 7 y Figura 6).
]

#cert_box(title: "Caja paramétrica, desigualdades acopladas, 64 bandas externas y geometría de las 1 054 hojas")[
  La caja paramétrica extendida es $tilde(cal(P)) = [0.749, 0.751]_(A_G) times [0.349, 0.351]_(A_B) times [0.9199, 0.9201]_q times [0.9699, 0.9701]_beta times [0.6999, 0.7001]_eta$. Las *64 bandas externas* corresponden a $8$ sub-bandas contiguas de $[beta_-, beta_+]$ por cada uno de los $8$ valores de $p$. En cada banda, la pareja $(B_(G,theta), B_(B,theta))$ satisface el sistema acoplado sobre $M times [b, y_"max"]$ (con extensión constante $B_(omega, theta) (K') = B_(omega, theta) (h)$ para $K' >= h$):
  $ B_(G,theta)(K) >= u(c_G, L) + beta [(1 - p) B_(G,theta)(K') + p B_(B,theta)(K')], \
    B_(B,theta)(K) >= u(c_B, L) + beta [p_"rec" B_(G,theta)(K') + (1 - p_"rec") B_(B,theta)(K')], $
  acoplado análogamente a $(Psi_G, Psi_B)$ y $(W_G, W_B)$ para el cálculo de $epsilon.alt_0^"comp"$ del Corolario 2. La necesidad de particionar $H_(1,B)$ en *$1 thin 054$ hojas continuas* (entre $128$ y $147$ hojas por valor de $p$) obedece a una razón económica y geométrica precisa: en recesión severa ($A_B = 0.35$), el producto marginal del capital apenas sostiene el consumo, dejando un margen mínimo de salida adversa sumamente ajustado ($+0.00015$) cerca de la frontera donde el planificador recesivo desearía desacumular por debajo de $h = 0.28$.
]

#figure(
  table(
    columns: (0.50fr, 0.80fr, 0.68fr, 0.85fr, 0.72fr, 0.76fr, 0.78fr, 0.78fr, 0.85fr),
    inset: 4.2pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 7.8pt)[$p$],
      text(fill: white, weight: "bold", size: 7.8pt)[$(T_G, T_B)_"aff"$],
      text(fill: white, weight: "bold", size: 7.8pt)[$epsilon.alt_(0,"aff")$],
      text(fill: white, weight: "bold", size: 7.8pt)[$E[tau]_"aff"$],
      text(fill: white, weight: "bold", size: 7.8pt)[$(T_G^*, T_B^*)$],
      text(fill: white, weight: "bold", size: 7.8pt)[$epsilon.alt_0^"comp"$],
      text(fill: white, weight: "bold", size: 7.8pt)[$E[tau]_"comp"$],
      text(fill: white, weight: "bold", size: 7.8pt)[$E_"VFI" [tau]$],
      text(fill: white, weight: "bold", size: 7.8pt)[$H_(1,B,"32bx")$],
    ),
    [$0.0\%$], [$21, 45$], [$0.0331$], [$1 thin 480.3$], [$5, 5$], [$0.3988$], [*$35.1$*], [$5.92$], [$+0.00017$],
    [$0.5\%$], [$22, 46$], [$0.0319$], [$1 thin 565.0$], [$5, 5$], [$0.3965$], [*$35.3$*], [$5.90$], [$+0.00019$],
    [$1.0\%$], [$22, 47$], [$0.0306$], [$1 thin 665.0$], [$5, 5$], [$0.3952$], [*$35.4$*], [$5.89$], [$+0.00015$],
    [$1.5\%$], [$22, 48$], [$0.0291$], [$1 thin 784.9$], [$5, 5$], [$0.3917$], [*$35.7$*], [$5.88$], [$+0.00045$],
    [$2.0\%$], [$23, 49$], [$0.0276$], [$1 thin 920.7$], [$5, 5$], [$0.3917$], [*$35.7$*], [$5.86$], [$+0.00196$],
    [$5.0\%$], [$26, 57$], [$0.0213$], [$2 thin 860.9$], [$5, 5$], [$0.4088$], [*$36.7$*], [$5.81$], [$+0.00394$],
    [$8.0\%$], [$29, 67$], [$0.0151$], [$4 thin 688.6$], [$5, 5$], [$0.3989$], [*$37.6$*], [$5.86$], [$+0.00903$],
    [$12.0\%$], [$34, 88$], [$0.0069$], [$13 thin 322.8$], [$6, 6$], [$0.3869$], [*$38.8$*], [$5.87$], [$+0.00023$],
  ),
  caption: [Tabla 7: Compresión estocástica del Caso 3: barrera afín analítica frente a barreras acopladas CEGIS-LP $(B_(G, theta), B_(B, theta))$ ($T_0^"opt" in {14, 15}$) y óptimo de malla $max_(M times {G, B}) E_"VFI" [tau]$ (alcanzado desde el estado recesivo $B$), reduciendo $E[tau]$ de $13 thin 322.8$ a $38.8$ períodos en $p = 12\%$.],
)

#v(0.2em)
#figure(
  image("fig_markov_es.svg", width: 92%),
  caption: [Figura 6: Caso 3 acoplado de Markov $(G, B)$. (a) Compresión de $42 times$ a $343 times$ de la cota superior de $E[tau]$ frente al óptimo VFI en escala logarítmica. (b) Barreras acopladas $(B_(G,theta), B_(B,theta))$ frente a $(W_G, W_B)$ en $p = 12\%$ (inserto: distribución de las $1 thin 054$ hojas continuas en $H_(1,B)$).],
)

=== Caso 5: Ruina Endógena Dependiente del Estado $p(K) = p bold(1)_(K < 0.28)$

A diferencia del Caso 2 (donde el riesgo de quiebra exógeno $p$ se cancela aditivamente mediante descuento efectivo $tilde(beta)_p$), modelamos aquí una economía en la que cruzar la escala segura $H = [0.28, oo)$ *elimina el riesgo existencial*: el peligro anual de ruina con valor de continuación $V_"ruin" = -60 < V(K)$ actúa únicamente sobre el estado vulnerable actual $K_t < 0.28$, obedeciendo la ecuación de Bellman explícita:
$ V(K) = max_((K', L)) { u(c, L) + beta [(1 - p(K)) V(K') + p(K) V_"ruin"] }, #h(12pt) p(K) = p bold(1)_(K < 0.28), #h(8pt) V_"ruin" = -60. $
Aparece entonces una prima endógena de supervivencia $V(K) - V_"ruin" >= 16.4 > 0$ que rompe la neutralidad de $V_"ruin"$ e induce una fuerte *«huida endógena hacia la seguridad»*: en la VFI continua de referencia (Tabla 8 y Figura 7), al encenderse el riesgo endógeno ($p = 1\%$), la inversión óptima salta de $K'(0.10) = 0.13364$ a $0.13719$ ($+2.66\%$) y el trabajo sube de $0.6626$ a $0.7079$, acortando el tiempo óptimo de escape hacia $H$ de *$4$ a $3$ períodos*.

#thm_box("Proposición", "9", [Certificación CEGIS-LP bajo ruina endógena $p(K) = p bold(1)_(K < 0.28)$ ($V_"ruin" = -60$, Caso 5)])[
  Para todo $p in {1\%, 2\%, 5\%, 8\%}$ sobre la caja paramétrica completa $cal(P)$, el motor CEGIS-LP certifica sin desplazamientos aditivos el techo global $Psi$ ($d_"ub,iv"^Psi <= -0.000100$), los testigos diferenciados $(W_M, W_H)$ por debajo y por encima de $h = 0.28$, la barrera de permanencia $B_theta$ ($d_"ub,iv"^B <= -0.000200$), derivadas $< b$ y $< h$, y márgenes positivos de salida adversa en $M$, $H_1$ y $H_2$:
  1. En los cuatro regímenes se certifica el plazo comprimido uniforme *$T^* = 5$* períodos, arrojando cotas garantizadas de supervivencia $(1 - p)^5$ (redondeadas estrictamente hacia abajo): $>= 95.09\%$ ($p=1\%$, exacto $0.950990$), $>= 90.39\%$ ($p=2\%$, exacto $0.903921$), $>= 77.37\%$ ($p=5\%$, exacto $0.773781$) y $>= 65.90\%$ ($p=8\%$, exacto $0.659082$).
  2. Todos los márgenes de salida adversa sobre el testigo permanecen estrictamente positivos hasta $p = 8\%$ ($M >= +0.4021$, $H_1 >= +0.3046$, $H_2 >= +2.8521$).
]

#cert_box(title: [Acoplamiento en $h = 0.28$ e invarianza de la cota $(1 - p)^(T^*)$ (Caso 5)])[
  Para manejar la discontinuidad de $p(K)$ en $h = 0.28$, el testigo se desacopla en dos ramas continuas pegadas en la frontera segura: en $K < 0.28$, $W_M (K)$ incorpora el descuento amortiguado $(1 - p) V(K') + p V_"ruin"$, mientras que en $K >= 0.28$ ($H_1 union H_2$), $W_H (K)$ evalúa la economía libre de ruina ($p = 0$) y $Psi$ satisface ambas ramas de Bellman con copia de seguridad en el límite izquierdo $h^-$ (y sin riesgo en $h^+$). Asimismo, la cota $(1 - p)^(T^*)$ vale idénticamente tanto bajo exposición dependiente del estado actual $p(K_t)$ como del estado sucesor $p(K_(t+1))$: toda trayectoria que permanece en $M$ durante a lo sumo $T^*$ períodos antes de alcanzar $H$ acumula a lo sumo $T^*$ exposiciones sucesivas bajo $p(K_t)$ (y a lo sumo $T^* - 1$ bajo $p(K_(t+1))$, pues el salto de entrada a $H$ ya no enfrenta riesgo), con probabilidad condicional $1 - p$ de no quiebra en cada paso ($K_t < 0.28$ para $0 <= t < tau_H <= T^*$), de modo que $(1 - p)^(T^*)$ constituye una cota inferior válida en ambos regímenes.
]

#v(0.2em)
#figure(
  table(
    columns: (0.60fr, 0.85fr, 0.85fr, 0.78fr, 0.62fr, 0.58fr, 0.88fr, 0.82fr, 0.78fr, 0.78fr),
    inset: 4.2pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 7.9pt)[$p$],
      text(fill: white, weight: "bold", size: 7.9pt)[$S_"endo"$ (VFI)],
      text(fill: white, weight: "bold", size: 7.9pt)[$K'(0.10)$],
      text(fill: white, weight: "bold", size: 7.9pt)[$L(0.10)$],
      text(fill: white, weight: "bold", size: 7.9pt)[$tau_"VFI"$],
      text(fill: white, weight: "bold", size: 7.9pt)[$T^*$],
      text(fill: white, weight: "bold", size: 7.9pt)[$Pr("surv")$],
      text(fill: white, weight: "bold", size: 7.9pt)[Sal. $M$],
      text(fill: white, weight: "bold", size: 7.9pt)[Sal. $H_1$],
      text(fill: white, weight: "bold", size: 7.9pt)[Sal. $H_2$],
    ),
    [$0.0\%$], [$0.001588$], [$0.13364$], [$0.6626$], [$4$], [---], [$100.0\%$], [---], [---], [---],
    [$1.0\%$], [$0.001766$], [$0.13719$], [$0.7079$], [$3$], [$5$], [$>= 95.09\%$], [$+0.8004$], [$+0.305$], [$+2.852$],
    [$2.0\%$], [$0.002003$], [$0.13706$], [$0.7061$], [$3$], [$5$], [$>= 90.39\%$], [$+0.7518$], [$+0.305$], [$+2.852$],
    [$5.0\%$], [$0.002996$], [$0.13670$], [$0.7011$], [$3$], [$5$], [$>= 77.37\%$], [$+0.5752$], [$+0.305$], [$+2.852$],
    [$8.0\%$], [$0.004434$], [$0.13634$], [$0.6965$], [$3$], [$5$], [$>= 65.90\%$], [$+0.4021$], [$+0.305$], [$+2.852$],
  ),
  caption: [Tabla 8: Ruina endógena $p(K) = p bold(1)_(K < 0.28)$ con $V_"ruin" = -60$ (Caso 5): la VFI muestra huida endógena hacia $H$ ($tau_"VFI": 4 -> 3$) y CEGIS-LP certifica $T^* = 5$ en toda la caja $cal(P)$.],
)

#v(0.2em)
#figure(
  image("fig_endo_policy_es.svg", width: 100%),
  caption: [Figura 7: Mecanismo de huida endógena hacia la seguridad bajo $p(K) = p bold(1)_(K < 0.28)$ (Caso 5). (a) Desplazamiento ascendente de la función política $K'(K)$ entre $p = 0\%$ y $p = 1\%$. (b) Trayectoria discreta óptima desde $K_0 = 0.10$ hasta $h = 0.28$, reduciendo el escape de $4$ a $3$ períodos.],
)

// ============================================================================
// SECCIÓN 7: VERIFICACIÓN FORMAL EN LEAN 4, REPRODUCIBILIDAD Y LIMITACIONES
// ============================================================================
= Verificación Formal en Lean 4, Reproducibilidad y Limitaciones

== Formalización Mecanizada en Lean 4 y Auditoría Independiente

La integración de barreras afines cerradas, análisis asintótico exacto, teoría converso-estocástica y síntesis determinista CEGIS-LP auditada sin `libm` se completa con dos capas independientes de garantía formal y computacional:

1. *Formalización mecanizada en Lean 4 (`13` módulos, cero `sorry`):* El repositorio incorpora una formalización completa en **Lean 4 (`v4.36.0` + Mathlib4, carpeta `lean/`)** sin `sorry` y sin axiomas adicionales más allá de los tres fundamentos estándar del kernel (`[propext, Classical.choice, Quot.sound]`). Esta capa verifica formalmente toda la arquitectura matemática del artículo: la aritmética de logaritmos sin `libm` (`Lemma11`, Lema 11 de MR 2026), el techo analítico global sobre todo $(0, oo)$ mediante $131$ segmentos racionales (`Lemma12` + `Lemma12Cert`, Lema 12 de MR 2026), el Lema 1 y Teorema 1 (`Theorem1`), las Proposiciones 1 y 2 incluida la Tabla 2 (`Proposition1`, `Proposition2` + `Proposition2Cert`), el Teorema 2, Corolario 1 y la ley asintótica de segundo orden —Parte 1 y cota superior de Parte 2— (`Theorem2` + `Theorem2SecondOrder`), el Lema 2, Corolario 2 y Teorema 3 (`Stochastic`), la solidez CEGIS-PWL y certificación en kernel de la barrera $B_theta$ compacta de $22$ nodos del Caso 1A (`CEGIS` + `CEGISCert`), y la teoría estructural de las Proposiciones 3--9 (`Section5Theory`).

2. *Auditoría terminal desacoplada y reproducibilidad pública:* La separación estricta entre _Proposer_ y _Verifier_ garantiza que la validez de las Tablas 1--8 sea independiente del algoritmo de síntesis o del entorno de ejecución. Cualquier lector o árbitro puede verificar íntegramente el archivo autocontenido `cegis_certificates.json.xz` ($5.75$ MB, que almacena los certificados continuos completos de los Casos 1--6) ejecutando el script minimalista `audit_standalone.py` (`330` líneas en Python estándar, cero dependencias de terceros y logaritmo sin `libm` en Rust o modo `--pure-python`), inspeccionando las corridas en GitHub Actions (`.github/workflows/verify.yml`), o ejecutando la suite completa `python verify_all.py --full-audit`.

== Limitaciones del Método y Delimitación del Alcance

Un análisis riguroso del marco desarrollado debe explicitar *cuatro* limitaciones estructurales relevantes para futuras extensiones:
1. *Maldición de la dimensionalidad en el verificador Branch-and-Bound:* Aunque la auditoría B&B 3D sobre $(K, K', L)$ certifica el espacio continuo de acciones con alta eficiencia en una dimensión de estado continuo ($K in R_(>0)$ y estado discreto finito $omega in {G, B}$), extender directamente la partición de intervalos de primer paso a modelos con $d >= 2$ variables de estado continuas (por ejemplo, capital físico y capital humano, deuda pública o acervos de I+D) enfrenta un crecimiento exponencial del número de hojas en $(K_1, dots, K_d, K'_1, dots, K'_d, L)$. La síntesis de barreras separables por estructura o relajaciones polinomiales SOS constituye una línea abierta natural para $d >= 2$.
2. *Costo de partición en cajas paramétricas anchas y regiones límite:* Como ilustra el Caso 6 (Tabla 5), ensanchar simultáneamente las bandas paramétricas en un factor $10 times$ eleva el número de subcajas requeridas de $8$ (`MR_Box_7_1`, $29.9$ s de síntesis) a $128$ (`Macro_10x_Box`, $745.7$ s), mientras que la sensibilidad en el estado recesivo $B$ sobre $H_(1,B)$ exige $1 thin 054$ hojas continuas en el Caso 3 ($2 thin 013$ s de re-verificación independiente). Más aún, en Markov la cota estacionaria de un paso $E[tau] <= 35.1"–"38.8$ conserva un factor $approx 6 times$ frente al óptimo verdadero de malla ($E_"VFI" [tau] approx 5.81"–"5.92$), susceptible de compresión adicional mediante barreras estocásticas no estacionarias.
3. *Dependencia de los cierres analíticos respecto a la CES armónica ($rho = -1$):* Mientras la arquitectura computacional CEGIS-LP es agnóstica a la forma funcional de $F_A (K, L)$ (requiriendo únicamente monotonicidad y cotas de derivada por intervalos), varios resultados analíticos cerrados —especialmente la expresión explícita del Wronskiano $Q_X (K)$ en la Proposición 2, la forma racional de $kappa_A$ y las constantes explícitas en la Proposición 1— explotan el álgebra cerrada de la tecnología CES con $rho = -1$ ($sigma = 1\/2$). El Teorema 2 y el Corolario 1 permanecen válidos para todo $d = -rho > 0$ arbitrario, pero la extensión de las salidas adversas de la Sección 3 a $rho != -1$ requiere adaptar la parametrización del Wronskiano.
4. *Frontera explícita de la Base de Cómputo Confiable (TCB) fuera de Lean 4:* Los únicos elementos que permanecen fuera de la verificación directa en el kernel de Lean 4 son dos piezas bien delimitadas: (i) la cota inferior afilada de la Parte 2 de la Observación 1 (mantenida explícitamente como heurística respaldada numéricamente hasta $A = 10^8$), y (ii) la re-auditoría de las tablas numéricas masivas de `cegis_certificates.json.xz`, cuya TCB residual queda reducida al script minimalista `audit_standalone.py` y al cálculo de intervalos sin `libm`.

Para preservar la unidad formal del manuscrito en torno a planificación óptima con trabajo endógeno, leyes asintóticas de potencia y certificados estocásticos de Doob, las extensiones hacia economías descentralizadas con fragmentación de firmas, curvas institucionales en forma de U bajo externalidades o crecimiento balanceado de tipo _Red Queen_ quedan delimitadas fuera de este trabajo.

// ============================================================================
// SECCIÓN 8: CONCLUSIONES
// ============================================================================
= Conclusiones

Más allá de su aplicación canónica al modelo MVS de Milei y Reidel (2026), la combinación de análisis asintótico puro, teoría converso-estocástica de Doob y síntesis adaptativa determinista CEGIS-LP auditada sin `libm` establece un marco general y reproducible para certificar barreras de primer paso en programación dinámica no convexa. Resumimos cinco conclusiones centrales:

1. *Afilamiento determinista y cierre casi completo del corredor de Skiba:* La barrera afín de un paso $B_1$ (*Teorema 1*) reduce exactamente a la mitad la cota analítica ($tau_H <= 23$), la Proposición 1 fija $c < 0.25$ y certifica $tau_(.1) <= 9$ en $M_0$, el Wronskiano cierra las salidas adversas (*Proposición 2*), CEGIS-LP comprime el plazo en $M$ hasta $T_"full" = 5$ explicando la brecha frente a la malla mediante cadenas no estacionarias ($T_"ns" (theta_0) = 4 = tau_H^"VFI"$, *Proposición 3*), y la cascada de $5$ etapas desde $b_"ext" = 0.0030$ (*Proposición 4*) cierra el $99.5\%$ de la brecha hasta $S_A$ con $T_"total" <= 52$.
2. *Resolución asintótica pura y ley de segundo orden ($A -> oo$):* El *Teorema 2* y el *Corolario 1* demuestran la equivalencia límite $A^2 S_A^"fix" (1) -> A^2 S_A -> 0.000800$ para todo $beta theta > 1$, prueban analíticamente sin VFI que $S_A^"fix" (1) < S_A$ para todo $A$ grande vía $T_M (A) = O(log log A)$, y la *Observación 1* explica cuantitativamente la persistencia del $+3.9\%$ en $A = 10^8$ y el límite estacionario $L_"ss" = 7\/9$.
3. *Completitud de Doob y compresión de Markov:* El *Teorema 3* acopla las súper-barreras de supermartingala directamente a la selección endógena de políticas óptimas bajo **(A1)--(A3)**, y las parejas acopladas $(B_(G,theta), B_(B,theta))$ (*Proposición 8*) comprimen la cota esperada en Markov hasta $p = 12\%$ en más de dos órdenes de magnitud ($E[tau] <= 35.1"–"38.8$, frente a $E_"VFI" [tau] approx 5.81"–"5.92$).
4. *Dicotomía económica bajo incertidumbre y ruina endógena:* Frente al colapso de inversión bajo ruina exógena invariante a $V_"ruin"$ (*Proposición 7*), tanto la recesión recuperable de Markov como la ruina endógena $p(K) = p bold(1)_(K < 0.28)$ (*Proposición 9*) desencadenan una *huida precautoria hacia la seguridad* que acorta el escape óptimo de VFI de $4$ a $3$ pasos y mantiene supervivencia garantizada de Doob $>= 90.39\%$ en $p = 2\%$.
5. *Transferibilidad, escalabilidad y verificación formal:* Al prescindir de redes neuronales en favor de programación lineal dispersa determinista con auditoría continua por intervalos, el marco se transfiere sin ajustes ad hoc al régimen híbrido CES--AK (*Proposición 5*), escala a cajas paramétricas $10 times$ anchas (`Macro_10x_Box`, $128$ subcajas, $T_"full" = 6$, *Proposición 6*) y queda respaldado por una formalización completa en Lean 4 (`13` módulos, `0` `sorry`) y auditoría independiente reproducible.

// ============================================================================
// APÉNDICE TÉCNICO A
// ============================================================================
#pagebreak()
#counter(heading).update(0)
#set heading(numbering: "A.1.")
= Apéndice Técnico

== Desambiguación Notacional

#figure(
  table(
    columns: (1.1fr, 1.8fr, 2.2fr),
    inset: 5.5pt,
    align: left,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.6pt)[Símbolo],
      text(fill: white, weight: "bold", size: 8.6pt)[Significado en este Artículo],
      text(fill: white, weight: "bold", size: 8.6pt)[Notas / Rango Calibrado],
    ),
    [$b, h$], [Bordes de la región $M = [b, h)$], [$b = 0.10$, $h = 0.28$; $M_0 = [0.05, 0.10)$; $H_1 = [0.28, 0.80)$],
    [$B_0, B_1, B_theta$], [Barreras de permanencia en $M$], [2 pasos ($-38.14$), afín ($[-43.36, -43.05]$), LP $57$ ($22$ comp.)],
    [$Psi, W$], [Techo (súper-barrera) y testigo factible], [Funciones continuas `log-PWL` certificadas en todo $(0, oo)$],
    [$cal(S)(K)$], [Recurso virtual mayorante (Prop. 2)], [$q_+ K + F_(A_+) (K, l_0) + (1 - l_0) t(K)$ (distinto de $S_A$)],
    [$cal(P), tilde(cal(P))$], [Cajas compactas de parámetros], [$A_G in [0.749, 0.751]$, $A_B in [0.349, 0.351]$, $q, beta, eta$ en $plus.minus 10^(-4)$],
    [$S_A, S_A^"fix" (overline(L))$], [Umbrales de Skiba endógeno y fijo], [Prueba pura $S_A^"fix" (1) < S_A$; 2.º orden $Delta_k$ ($beta theta > 1$)],
    [$Delta W_A^(pi^+), Delta W_A^+$], [Diferenciales variacionales en $S_A$], [Escala $beta^(T_M) g_(T_M) >> A^(-1)$ ($T_M = O(log log A)$)],
    [$p, p_"rec", p(K)$], [Riesgo de ruina, Markov y endógeno], [Ruina: $[0, 2\%]$; Markov: $p <= 12\%$; Endóg.: $p bold(1)_(K<0.28)$],
    [$epsilon.alt_0, E[tau]_"comp"$], [Brecha de Doob y cota Markov], [$epsilon.alt_0^"comp" >= 0.3869$; $E[tau] <= 35.1"–"38.8$ en $(B_(G,theta), B_(B,theta))$],
  ),
  caption: [Tabla A.1: Desambiguación notacional utilizada en el manuscrito.],
)

== Fórmulas Explícitas de $E^+$ y Criterio de Wronskiano (Prop. 2)

Explicitamos las fórmulas de salida adversa utilizadas en la Proposición 2. Dada la producción CES $F_A (K, l_0) = A (2 K l_0 \/ (K + l_0))^(3\/2)$ en nivel laboral fijo $l_0$, se definen el valor marginal del trabajo $t(K) = partial F_(A_+) \/ partial L (K, l_0)$, su primera derivada en $K$, $t'(K) = t(K) dot 5 l_0 \/ (2 K (K + l_0))$, el recurso virtual mayorante $cal(S)(K) = q_+ K + F_(A_+) (K, l_0) + (1 - l_0) t(K)$, el excedente de consumo $c_"sup" (K) = cal(S)(K) - a$, el consumo del testigo $c_X (K) = q_- K + F_(A_-) (K, l_X) - s_X$, y la demanda óptima de ocio restringida $omega^*(K, eta) = min{1, (1 - eta) c_"sup" (K) \/ t(K)}$. El verificador de intervalos evalúa tanto la identidad exacta interior cuando $omega^* < 1$ en todo el subintervalo como el término envolvente completo $-eta thin t'(K) omega^* \/ c_"opt"$ cuando $omega^*$ puede alcanzar $1$, y certifica que el Wronskiano exacto del cociente $R_X (K) = (cal(S)(K) - a)\/c_X (K)$, dado por
$ Q_X (K) = cal(S)'(K) c_X (K) - c'_X (K) (cal(S)(K) - a), #h(12pt) Q'_X (K) = cal(S)''(K) c_X (K) - c''_X (K) (cal(S)(K) - a), $
mantiene $Q_X (K) < 0$, $Delta'_X (K) > 0$ y $Delta''_X (K) < 0$ en todo $[0.10, 0.28]$ y $[0.28, 0.80]$.

== Protocolo Reproducible, Logaritmo sin `libm` y Auditor Autocontenido

El paquete de software reproducible (`audit_standalone.py`, `cegis_synth.py`, `cegis_verifier.py`, `interval_audit.py`, `pwl_model.py`, `verify_all.py`, `generate_figures.py` y `rust_verifier/`) reproduce deterministamente (`seed = 42`) los $6$ casos, las tablas, los certificados y las $7$ figuras (#link("https://github.com/lordtiva/mvs-bellman-barriers")[`github.com/lordtiva/mvs-bellman-barriers`], archivo permanente en Zenodo con Concept DOI #link("https://doi.org/10.5281/zenodo.24464158")[`10.5281/zenodo.24464158`]):
1. *Propuesta determinista HiGHS-LP (_Proposer_):* Todas las síntesis en los Casos 1--6 se formulan como programas lineales dispersos en SciPy/HiGHS (`_eval_pwl_basis_sparse`) paralelizados sobre subcajas y bandas.
2. *Aritmética de intervalos libre de `libm`:* Para eliminar cualquier dependencia en la implementación `libm` del sistema operativo (`f64::ln` o `Decimal.ln`), tanto el núcleo Rust (`iv_ln_pt` en `rust_verifier/src/lib.rs`, compilado en `mvs_verifier.dll` mediante `python rust_verifier/build.py`) como el módulo `Decimal` de $50$ dígitos (`interval_audit.py`) calculan envolturas rigurosas de $log x$ reduciendo el argumento al rango $[1, 2)$ mediante potencias de $2$ y raíces cuadradas acotadas más serie truncada de $2 "atanh"((m-1)\/(m+1))$ con cota geométrica explícita de residuo (anchura máxima certificada $<= 10^(-47)$ en `Decimal` y $<= 2$ ULPs en IEEE-754 con signos acoplados de $beta$).
3. *Auditor minimalista de cero dependencias (`audit_standalone.py`):* El repositorio incluye un verificador puro de `330` líneas que únicamente importa módulos estándar de Python (`argparse`, `bisect`, `ctypes`, `concurrent.futures`, `decimal`, `json`, `lzma`, `math`, `os`, `time`), lee `cegis_certificates.json.xz` ($5.754$ MB) y soporta tanto el núcleo compilado en Rust como modo 100% Python (`--pure-python`, verificado en el Caso 4 en $75.01$ s). Ejecutando `python audit_standalone.py cegis_certificates.json.xz` se re-audita independientemente el Caso 1 en $49.80$ s, el Caso 2 en $7.81$ s, el Caso 3 en $2 thin 013.02$ s, el Caso 4 en $65.80$ s, el Caso 5 en $35.80$ s y el Caso 6 en $170.88$ s (`MR_Box_7_1` en $10.66$ s y `Macro_10x_Box` en $160.21$ s).

== Sensibilidad a la Probabilidad de Recuperación $p_"rec"$ (Tabla A.2)

La Tabla A.2 presenta la sensibilidad de la VFI estocástica continua de Markov en $p = 8.0\%$ al variar la probabilidad anual de recuperación $p_"rec"$ entre $0.20$ y $0.50$: cuanto menor es $p_"rec"$ (recesiones más persistentes), más fuerte es el incentivo precautorio de «huida hacia la seguridad» ($K'_G (0.10)$ sube de $0.13447$ a $0.13511$ y $L_G$ sube de $0.6726$ a $0.6803$).

#figure(
  table(
    columns: (1.0fr, 1.1fr, 1.1fr, 1.1fr, 1.2fr, 1.0fr),
    inset: 5.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.6pt)[$p_"rec"$ ($p=8\%$)],
      text(fill: white, weight: "bold", size: 8.6pt)[$S_G$],
      text(fill: white, weight: "bold", size: 8.6pt)[$S_("B,kink")$],
      text(fill: white, weight: "bold", size: 8.6pt)[$K_B^*$],
      text(fill: white, weight: "bold", size: 8.6pt)[$K'_G (0.10)$],
      text(fill: white, weight: "bold", size: 8.6pt)[$L_G$],
    ),
    [$0.2000$], [$0.001836$], [$0.00192$], [$0.00969$], [$0.13511$], [$0.6803$],
    [$0.3333$], [$0.001774$], [$0.00187$], [$0.00991$], [$0.13475$], [$0.6759$],
    [$0.5000$], [$0.001735$], [$0.00182$], [$0.01038$], [$0.13447$], [$0.6726$],
  ),
  caption: [Tabla A.2 (extracto VFI Markov): Sensibilidad respecto a $p_"rec"$ evaluada en $p = 8.0\%$.],
)

== Esquema de Demostración de la Ley de Segundo Orden (Observación 1)

Detallamos aquí la arquitectura de tres piezas demostrada y formalizada sin `sorry` en `lean/MVS/Theorem2SecondOrder.lean` para todo parámetro CES con $beta theta > 1$ (sin requerir $beta lambda_K >= 1$). Sea $k_* := (delta\/c_K)^(1\/r)$ el umbral físico de reposición donde el producto neto normalizado $g(k) := c_K k^theta - delta k$ satisface $g(k_*) = 0$ y $g'(k_*) = theta c_K k_*^r - delta = r delta = lambda_K - 1$ (con $lambda_K := q + theta delta = 1 + r delta > 1$), y sean los exponentes exactos $kappa := |log beta| \/ log theta in (0, 1)$ y $mu_K := |log beta| \/ log lambda_K > 0$:

1. *Definición de objetos y exponente exacto $1 - kappa$ en la Fase II (Pieza 1):* Si a lo largo de la Fase II una senda verifica $k_(j+1) >= alpha k_j^theta$ para un factor neto constante $alpha > 0$ (por ejemplo $alpha = (1 - epsilon.alt_1\/2) c_K \/ 2$ en el ahorro mitad-mitad), el reescalado exacto $y_j := alpha^(1\/r) k_j$ satisface la recurrencia homogénea sin pérdida de exponente $y_(j+1) >= y_j^theta$, rindiendo $y_j >= y_0^(theta^j)$. Esto evita sustituir $theta$ por $tilde(theta) < theta$ y fija el tiempo de alcance hasta la meseta macroscópica en $J(A) <= (log log A)\/(log theta) + O(1)$, con recompensa descontada $beta^(J(A)) log A >= c_0 (log A)^(1 - kappa)$ y cota superior emparejada $O((log A)^(1 - kappa))$ vía techo macroscópico $F_A (K, L) <= A c_K c_w^(-theta\/d)$.

2. *Cota superior de $Delta_k (A)$ mediante política explícita (Pieza 2):* Sea $x_t := k_t - k_* >= 0$ el exceso de capital sobre $k_*$ partiendo de $x_0 = Delta_k := A^(1\/r) S_A - k_*$. Por convexidad de $g$ en $[k_*, k_* + epsilon.alt]$, vale $g(k_* + x) >= (lambda_K - 1) x + m x^2$ mientras la penalización CES frente al límite $c_K k^theta$ es $O(A^(-d\/r))$. Para cualquier $Delta_k < epsilon.alt$, fijando $T := ceil(log(2 epsilon.alt \/ Delta_k) \/ log lambda_K)$ se define la política explícita linealizada:
   $ c_t^* := ((1 - beta) / (1 - beta^T)) lambda_K (beta lambda_K)^t (Delta_k - epsilon.alt / lambda_K^T), #h(12pt) x_(t+1) = lambda_K x_t - c_t^*. $
   Esta política alcanza exactamente $x_T = epsilon.alt$ manteniendo $x_t >= ((1 - beta)\/2) Delta_k$, con descuento $beta^T >= (Delta_k \/ (2 lambda_K epsilon.alt))^(mu_K)$ y utilidad acumulada $>= (eta\/(1 - beta)) log Delta_k - C_"pol"$. Combinando con la Pieza 1 en $k_* + epsilon.alt$ y comparando contra la cota de extinción _cake-eating_ $C_"ext"$, emerge la desigualdad de balance:
   $ (eta) / (1 - beta) log Delta_k - C_"pol" + (Delta_k / (2 lambda_K epsilon.alt))^(mu_K) [c_"lo" (log A)^(1 - kappa) - C_"lo"] > C_"ext", $
   cuya inversión algebraica entrega rigurosamente $Delta_k (A) <= C_+ ([log log A] \/ [(log A)^(1 - kappa)])^(1\/mu_K)$.

3. *Cota inferior de $Delta_k (A)$ vía coordenada cuadrática $phi(x)$ y papel de $phi.alt(Delta_k)$ (Pieza 3):* En $[k_*, k_* + epsilon.alt]$, la acotación superior de $g''$ ($g''(k) <= 2 M$) acota $g(k_* + x) <= (lambda_K - 1) x + M x^2$. Introduciendo la coordenada cuadrática sub-linealizada $phi(x) := x - C x^2$ con $C := M \/ (lambda_K (lambda_K - 1))$, una cancelación algebraica exacta elimina el término $x^2$:
   $ phi(lambda_K x + M x^2) - lambda_K phi(x) = -2 C lambda_K M x^3 - C M^2 x^4 <= 0 #h(8pt) (x >= 0). $
   De aquí se deduce el paso contractivo $phi(x_(t+1)) <= lambda_K phi(x_t) - (1\/2) c_t$ mientras $lambda_K x_t + M x_t^2 <= 1\/(4 C)$, lo que telescopa exactamente en el presupuesto:
   $ 1 / 2 sum_(t=0)^(T-1) (c_t) / (lambda_K^(t+1)) <= phi(Delta_k) - (phi(epsilon.alt)) / (lambda_K^T) <= Delta_k - (phi(epsilon.alt)) / (lambda_K^T). $
   El término $t = 0$ da inmediatamente $c_0 <= 2 lambda_K Delta_k$ (base de la cota superior de Parte 2 vía envolvente de Milgrom--Segal), y acotando la suma logarítmica con $log(c_t\/w_t) <= c_t\/w_t - 1$ sobre pesos tangentes $w_t$ se obtiene la ecuación de balance invertida $(eta\/(1 - beta)) log(k_* \/ Delta_k) + C_0 approx Delta_k^(mu_K) [C_oo (log A)^(1 - kappa) + C_"const"]$, donde $phi.alt(Delta_k)$ denota la corrección relativa del consumo óptimo inicial $c_0 \/ Delta_k$ (de orden $(log log A)^(-1)$ al despejar la fracción residual de presupuesto). En la Parte 1, al tomar logaritmos en la ecuación de balance, $log phi.alt(Delta_k) = O(log log log A)$ es estrictamente subdominante frente a $log log A$, dejando intacto el exponente de $Delta_k (A) asymp ([log log A] \/ [(log A)^(1 - kappa)])^(1\/mu_K)$. En cambio, en la cota inferior de la Parte 2 (donde se evalúa directamente la derivada envolvente $partial_K u_"red" ~ 1\/c_0$), $phi.alt(Delta_k) asymp (log log A)^(-1)$ entra multiplicativamente en primer orden sin logaritmo, explicando de forma natural por qué la razón sin corregir $(S_A - S_A^"fix" (1)) \/ (S_A dot Delta_k dot Delta W_A^+)$ desciende gradualmente de $29.35$ a $22.36$ conforme $A$ crece hasta $10^8$.

// ============================================================================
// REFERENCIAS BIBLIOGRÁFICAS
// ============================================================================
#v(0.8em)
#heading(numbering: none)[Referencias]
#set text(size: 9.4pt)

- Abate, A., Ahmed, D., Giacobbe, M., & Peruffo, A. (2021). Formal synthesis of Lyapunov neural networks. _IEEE Control Systems Letters_, 5(3), 773--778.
- Acemoglu, D. (2009). _Introduction to Modern Economic Growth_. Princeton University Press.
- Akao, K., Ishii, H., Kamihigashi, T., & Nishimura, K. (2022). Existence of an optimal path in a #box[continuous-time] nonconcave Ramsey model. _Pure and Applied Functional Analysis_, 7(6), 1939--1952.
- Akao, K., Kamihigashi, T., & Nishimura, K. (2011). Monotonicity and continuity of the critical capital stock in the Dechert--Nishimura model. _Journal of Mathematical Economics_, 47(6), 677--682.
- Aubin, J.-P. (1991). _Viability Theory_. Birkhäuser.
- Dechert, W. D., & Nishimura, K. (1983). A complete characterization of optimal growth paths in an aggregated model with a non-concave production function. _Journal of Economic Theory_, 31(2), 332--354.
- Doob, J. L. (1953). _Stochastic Processes_. Wiley.
- Hernández-Lerma, O., & Lasserre, J. B. (1996). _Discrete-Time Markov Control Processes: Basic Optimality Criteria_. Springer.
- Huangfu, Q., & Hall, J. A. J. (2018). Parallelizing the dual revised simplex method. _Mathematical Programming Computation_, 10, 119--142.
- Kamihigashi, T., & Roy, S. (2007). A nonsmooth, nonconvex model of optimal growth. _Journal of Economic Theory_, 132(1), 435--460.
- Kraay, A., & McKenzie, D. (2014). Do poverty traps exist? Assessing the evidence. _Journal of Economic Perspectives_, 28(3), 127--148.
- Kushner, H. J. (1967). _Stochastic Stability and Control_. Academic Press.
- Majumdar, M., & Mitra, T. (1982). Intertemporal allocation with a non-convex technology: The aggregative framework. _Journal of Economic Theory_, 27(1), 101--136.
- Meyn, S. P., & Tweedie, R. L. (2009). _Markov Chains and Stochastic Stability_ (2.ª ed.). Cambridge University Press.
- Milei, J., & Reidel, D. (2026). _Minimum Viable Scale: Bellman Barriers and the Economics of Survival_ (edición de octubre de 2026). Manuscrito de trabajo (`minscale.org/paper/mvs.pdf`).
- Milgrom, P., & Segal, I. (2002). Envelope theorems for arbitrary choice sets. _Econometrica_, 70(2), 583--601.
- Moore, R. E., Kearfott, R. B., & Cloud, M. J. (2009). _Introduction to Interval Analysis_. SIAM.
- Prajna, S., Jadbabaie, A., & Pappas, G. J. (2007). A framework for worst-case and stochastic safety verification using barrier certificates. _IEEE Transactions on Automatic Control_, 52(8), 1415--1428.
- Ravanbakhsh, H., & Sankaranarayanan, S. (2019). Learning control Lyapunov functions from counterexamples and demonstrations. _Autonomous Robots_, 43, 275--307.
- Skiba, A. K. (1978). Optimal growth with a convex-concave production function. _Econometrica_, 46(3), 527--539.
- Solar-Lezama, A. (2008). _Program Synthesis by Sketching_. Tesis doctoral, UC Berkeley.
- Tucker, W. (2011). _Validated Numerics: A Short Introduction to Rigorous Computations_. Princeton University Press.
- Wagener, F. O. O. (2003). Skiba points and heteroclinic bifurcations, with applications to the shallow lake system. _Journal of Economic Dynamics and Control_, 27(9), 1533--1561.
- Williams, D. (1991). _Probability with Martingales_. Cambridge University Press.
