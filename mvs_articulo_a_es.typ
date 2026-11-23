#set page(
  paper: "a4",
  margin: (top: 2.3cm, bottom: 2.3cm, left: 2.4cm, right: 2.4cm),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 8.5pt, fill: luma(110), style: "italic")
      #grid(
        columns: (1fr, 1fr),
        align: (left, right),
        [Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica],
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
    Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada bajo Rendimientos Crecientes
  ]
  #v(0.45em)
  #text(size: 11pt, style: "italic", fill: rgb("#1f4e78"))[
    Extensiones Analíticas, Síntesis Adaptativa CEGIS-PWL y Certificados de Intervalos sobre _Minimum Viable Scale_ (Milei y Reidel, 2026)
  ]
  #v(0.8em)
  #text(size: 11pt, weight: "bold")[Marcelo Segura]
  #v(0.2em)
  #text(size: 9.5pt, fill: luma(90))[Manuscrito Técnico — Versión Autónoma Reproducible (Artículo A)]
  #v(0.2em)
  #text(size: 9pt, fill: luma(110))[Noviembre de 2026]
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
    Presentamos un conjunto unificado de afilamientos analíticos, teoremas asintóticos y síntesis adaptativa determinista mediante programación lineal dispersa guiada por contraejemplos (_CEGIS-LP / log-PWL_) sobre el modelo de programación dinámica no convexa con escala mínima viable (_Minimum Viable Scale_, MVS) de Milei y Reidel (octubre de 2026). El artículo cierra cinco contribuciones de fondo. Primero, en el plano determinista, reemplazamos el bloque de dos pasos por una barrera afín cerrada de un paso (_Teorema 9\*_), reduciendo a la mitad la cota analítica ($tau_H <= 46 -> 23$), afilamos la región previa $M_0 = [0.05, 0.10)$ hasta $tau_(.1) <= 9$ (_Proposición 1\*_), comprimimos la barrera en $M$ vía _CEGIS-LP_ hasta $T_theta = 9$ y $T_"full" = 5$ (descomponiendo mediante barreras no estacionarias $\{J_k\}$ la brecha residual: $T_"ns" (cal(P)) = 5 -> T_"ns" (theta_0) = 4 = tau_H^"VFI"$), y cerramos el $99.5\%$ de la brecha $[0.0025, 0.10)$ de la Figura 6 de MR ($98.6\%$ del intervalo $(S_A, 0.10)$) extendiendo la cascada certificada casi hasta el punto de Skiba desde $b_"ext" = 0.0030$ (_Proposición 2\*_, $16$ subcajas, $T_"total" <= 52$). Segundo, resolvemos por vía analítica pura la Nota al pie 1 de MR (_Teorema 3\*_ y _Corolario 2\*_): demostramos sin recurrir a la VFI que el tiempo de escape productivamente óptimo cumple $T_"esc" (A) = O(log log A)$ y supera polilogarítmicamente a la cota armónica $Delta W_A^- = O(A^(-1))$, probando $S_A^"fix" (1) < S_A$ como teorema puro para todo $A$ grande, y formulamos una ley asintótica heurística de segundo orden para $A^(1\/r) S_A - (delta\/c_K)^(1\/r)$ validada cuantitativamente hasta $A = 10^8$ (_Observación 1_). Tercero, acoplamos la parada opcional de Doob (_Lema 2_) con su teorema converso estocástico (_Teorema 7\*_: equivalencia entre escape casi seguro en tiempo medio finito y existencia de super-barreras de supermartingala con brecha $epsilon.alt_0 > 0$), y sintetizamos parejas acopladas de barreras $(B_(G, theta), B_(B, theta))$ en Markov hasta $p = 12\%$ (_Caso 3_), comprimiendo $E[tau]$ de $1 thin 480"–"13 thin 323$ a $35.1"–"38.8$ períodos con auditoría completa de las $1 thin 054$ hojas continuas en $H_(1,B)$. Cuarto, explicitamos la invariancia exacta respecto a $V_"ruin"$ en ruina exógena (_Caso 2_, $60$ bandas, $T^*_"CEGIS" (2\%) = 5$) e incorporamos ruina endógena dependiente del estado $p(K) = p bold(1)_(K < 0.28)$ (_Caso 5_), donde aparece un incentivo endógeno de _huida hacia la seguridad_ ($tau_"VFI"$ cae de $4$ a $3$ y $T^* = 5$). Quinto, toda la síntesis opera 100% por LP determinista sin dependencias de aprendizaje profundo, implementamos `ln()` libre de `libm` por el Lema 11 de MR tanto en Rust como en `Decimal` de 50 dígitos, probamos escalabilidad en cajas anchas hasta $10 times$ (_Caso 6_, $128$ subcajas, $T_"full" = 6$), y entregamos un auditor minimalista autocontenido de 329 líneas sin dependencias externas (`audit_standalone.py`) que verifica el $100\%$ de los certificados comprimidos en `cegis_certificates.json.xz`.

    #v(0.3em)
    #text(weight: "bold", fill: rgb("#0b2c4d"))[Palabras clave:] Programación dinámica no convexa, puntos de Skiba, barreras de Bellman, CEGIS log-PWL, aritmética de intervalos, parada opcional de Doob, equivalencia asintótica CES.
  ],
)

// ============================================================================
// SECCIÓN 1: INTRODUCCIÓN Y CUADRO 1
// ============================================================================
= Introducción y Mapa Epistemológico

Los modelos de desarrollo e industrialización con rendimientos crecientes a escala exhiben trampas de pobreza y umbrales críticos de capital conocidos como puntos de Skiba o Dechert--Nishimura (Skiba, 1978; Dechert y Nishimura, 1983). En su monografía _Minimum Viable Scale: Bellman Barriers and the Economics of Survival_ (edición de octubre de 2026; revisada posteriormente como _Extinction and Escape under Increasing Returns_), Milei y Reidel —en adelante MR— sustituyen el cálculo heurístico en malla fija por un método constructivo de _First Passage Bellman Barriers_ (_Barreras de Bellman de Primer Paso_, FPBB): mediante barreras analíticas simples acotan la función valor óptima $V(K)$ desde abajo por testigos factibles $W(K)$ y desde arriba por techos de Bellman $Psi(K)$, extrayendo garantías rigurosas en tiempo finito sobre el plazo de escape desde la región de tránsito $M = [0.10, 0.28)$ hacia el umbral productivo $h = 0.28$ y sobre la extinción asintótica por debajo de la escala mínima viable $b = 0.10$.

Este artículo surge como extensión analítica y computacional directa de MR (octubre de 2026), manteniendo intactas su calibración paramétrica de referencia y la numeración de sus teoremas, cajas y notas, y organizando sus contribuciones en *tres ejes articulados en cinco avances metodológicos*:

1. *Afilamiento determinista de FPBB, cierre casi hasta el punto de Skiba y descomposición exacta ($46 -> 23 -> 9 -> 5 -> 4$):* Demostramos en la Sección 3 que la cota original $tau_H <= 46$ de MR (Sección 7.2, Teorema 9 y Apéndice F.3) sufre una pérdida artificial por el bloqueo algebraico de dos pasos ($B_0 = -38.144176$). Con la barrera afín de un paso $B_1 (K) = B_* - m_omega (h - K)$ (_Teorema 9\*_), cortamos el plazo máximo a la mitad exacta ($tau_H <= 23$) en forma cerrada; en $M_0 = [0.05, 0.10)$ fijamos la condición $c < 1 - L = 0.25$ y afilamos a $tau_(.1) <= 9$ (_Proposición 1\*_). En la Sección 5 (_Caso 1_), un motor 100% LP determinista (HiGHS, sin redes neuronales ni entrenamiento estocástico) sintetiza la tripleta $(B_theta, Psi, W)$ alcanzando $T_theta = 9$ y $T_"full" = 5$, y mediante cadenas no estacionarias de Bellman $\{J_k\}$ explicamos el residuo completo frente al límite de malla: $T_"ns" (cal(P)) = 5 -> T_"ns" (theta_0) = 4 = tau_H^"VFI"$. Más aún, la _Proposición 2\*_ encadena una cascada continua de $5$ etapas en $16$ subcajas desde $b_"ext" = 0.0030$ hasta $H = [0.28, oo)$ con plazo total $T_"total" <= 52$, cerrando el $99.5\%$ de la brecha $[0.0025, 0.10)$ de la Figura 6 de MR ($98.6\%$ del intervalo $(S_A, 0.10)$). Cerramos también el continuo de salidas adversas por Wronskiano (_Proposición 1\*\*_).

2. *Resolución asintótica pura de la Nota al pie 1 ($A -> oo$) y ley heurística de segundo orden:* En la Sección 4 abordamos la Nota al pie 1 de MR sobre trabajo elástico vs. trabajo fijo. El _Teorema 3\*_ (Parte 1) prueba la convergencia uniforme hacia $A^2 S_A^"fix" (1) -> (delta\/c_K)^(1\/r) = 0.000800$, y el _Corolario 2\*_ extiende la unicidad al régimen de paciencia débil $beta theta > 1$ vía envolvente de Milgrom--Segal. En la Parte 2 elevamos la desigualdad finita $S_A^"fix" (1) < S_A$ de criterio variacional asistido a *teorema analítico puro para todo $A$ suficientemente grande* mediante una cota explícita $T_"esc" (A) <= T_M (A) = O(log log A)$ a lo largo del óptimo productivo $pi^+$. Adicionalmente, formulamos una ley asintótica heurística de segundo orden (_Observación 1_) para el lento acercamiento ($+3.9\%$ en $A = 10^8$) y la brecha relativa $(S_A - S_A^"fix" (1)) \/ S_A$, validada hasta $A = 10^8$ con $L_"ss" = 7\/9$ y $Delta W_A^- = O(A^(-1))$.

3. *Teoría converso-estocástica de Doob, Markov comprimido, ruina endógena $p(K)$ y verificación estándar oro:* En la Sección 5 elevamos el _Lema 2_ mediante el _Teorema 7\*_ (equivalencia exacta entre escape casi seguro en tiempo medio uniformemente acotado y existencia de FPBB estocásticas estrictas de Doob, análogo estocástico del Teorema 7 de MR). Mediante CEGIS-LP ralo libre de aprendizaje profundo y aritmética de intervalos sin `libm` (Lema 11 de MR en Rust `f64::next_down`/`next_up` y `Decimal` de 50 dígitos), certificamos: (_Caso 2_) las $60$ bandas de ruina exógena sobre $[0\%, 2.0\%]$ ($T^*_"CEGIS" = 5$, explicitando invariancia a $V_"ruin"$); (_Caso 3_) el sistema de Markov $(G, B)$ hasta $p = 12\%$ con barreras acopladas $(B_(G, theta), B_(B, theta))$ que comprimen $E[tau]$ de $1 thin 480"–"13 thin 323$ a $35.1"–"38.8$ períodos ($epsilon.alt_0 >= 0.3869$), auditando las $1 thin 054$ hojas continuas en $H_(1,B)$; (_Caso 4_) régimen $A K$ híbrido ($T_"AK" = 4$); (_Caso 5_) ruina endógena dependiente del estado $p(K) = p bold(1)_(K < 0.28)$ con *huida hacia la seguridad* endógena ($T^* = 5$, $tau_"VFI"$ cae de $4$ a $3$); y (_Caso 6_) pruebas de estrés en cajas anchas hasta $10 times$ ($128$ subcajas, $T_"full" = 6$), verificables por separado con `audit_standalone.py` (329 líneas, $0$ dependencias externas).

#v(0.4em)
#figure(
  table(
    columns: (1.5fr, 1.35fr, 1.85fr, 1.7fr),
    inset: 5.5pt,
    align: left,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.6pt)[Resultado],
      text(fill: white, weight: "bold", size: 8.6pt)[Objeto / Dominio],
      text(fill: white, weight: "bold", size: 8.6pt)[Cota o Propiedad Probada],
      text(fill: white, weight: "bold", size: 8.6pt)[Método de Prueba],
    ),
    [#text(size: 8.4pt)[*Lema 1 & Teorema 9\**]], [#text(size: 8.4pt)[Barrera afín $B_1 (K)$ en $M$]], [#text(size: 8.4pt)[$B_1 >= -43.356$; $tau_H <= 23$]], [#text(size: 8.4pt)[Analítico cerrado (1 paso)]],
    [#text(size: 8.4pt)[*Proposición 1\* & $M_0$*]], [#text(size: 8.4pt)[Testigo afilado en $[0.05, 0.10)$]], [#text(size: 8.4pt)[$c < 0.25$; $tau_(.1) <= 9$ ($+0.5253$)]], [#text(size: 8.4pt)[Analítico + techo LP $Psi' >= 91.23$]],
    [#text(size: 8.4pt)[*Proposición 1\*\**]], [#text(size: 8.4pt)[Salidas $E^+(K, a; l_0)$ en $M, H_1$]], [#text(size: 8.4pt)[$Delta'' < 0$; $Q <= -0.04375$]], [#text(size: 8.4pt)[Wronskiano + `Decimal` 50 díg.]],
    [#text(size: 8.4pt)[*Teo. 3\* & Obs. 1*]], [#text(size: 8.4pt)[Escalado $A -> oo$, $beta theta > 1$]], [#text(size: 8.4pt)[$S_A^"fix" (1) < S_A$; $T_"esc" = O(log log A)$]], [#text(size: 8.4pt)[Asintótica pura + VFI $log k$ ($A <= 10^8$)]],
    [#text(size: 8.4pt)[*Prop. 2 (Caso 1A/1C)*]], [#text(size: 8.4pt)[LP determinista + cadena $\{J_k\}$]], [#text(size: 8.4pt)[$T_theta = 9$; $T_"full" = 5$; $T_"ns" = 5\/4$]], [#text(size: 8.4pt)[HiGHS-LP + B&B 3D (sin PyTorch)]],
    [#text(size: 8.4pt)[*Prop. 2\* (Caso 1B)*]], [#text(size: 8.4pt)[Cascada $[0.003, 0.28)$ ($16$ cajas)]], [#text(size: 8.4pt)[$T_"total" <= 52$; salida $>= +0.1326$]], [#text(size: 8.4pt)[5 etapas contiguas LP + Lema 11]],
    [#text(size: 8.4pt)[*Teorema 7\* (Converso)*]], [#text(size: 8.4pt)[FPBB estocástica de Doob]], [#text(size: 8.4pt)[Escape c.s. + $sup E[tau] < oo <==>$ FPBB]], [#text(size: 8.4pt)[Teoría estocástica bajo (A1)--(A3)]],
    [#text(size: 8.4pt)[*Lema 2, Cor. 3, Prop. 3*]], [#text(size: 8.4pt)[Ruina exóg. $p in [0, 2\%]$ ($60$ b.)]], [#text(size: 8.4pt)[Invariante $V_"ruin"$; $T^*_"CEGIS" = 5$]], [#text(size: 8.4pt)[Doob + CEGIS-LP + interv. Lema 11]],
    [#text(size: 8.4pt)[*Proposición 4 (Caso 3)*]], [#text(size: 8.4pt)[Markov $(G, B)$ hasta $p = 12\%$]], [#text(size: 8.4pt)[$E[tau] <= 35.1"–"38.8$; $1 thin 054$ hojas $H_(1,B)$]], [#text(size: 8.4pt)[$(B_(G,theta), B_(B,theta))$ acopladas + B&B 3D]],
    [#text(size: 8.4pt)[*Prop. 5 (Caso 4 AK)*]], [#text(size: 8.4pt)[Régimen híbrido CES--AK]], [#text(size: 8.4pt)[$Psi_"AK" (0.28) = +243.46$; $T_"AK" = 4$]], [#text(size: 8.4pt)[CEGIS-LP + rayo homogéneo 50 díg.]],
    [#text(size: 8.4pt)[*Prop. 6 (Caso 5)*]], [#text(size: 8.4pt)[Ruina endógena $p(K) = p bold(1)_(K<0.28)$]], [#text(size: 8.4pt)[Huida endógena; $T^* = 5$; surv. $90.4\%$]], [#text(size: 8.4pt)[VFI comparativa + CEGIS-LP]],
    [#text(size: 8.4pt)[*Prop. 7 (Caso 6)*]], [#text(size: 8.4pt)[Cajas anchas $10 times$ ($8 + 128$ bx)]], [#text(size: 8.4pt)[$T_"full" = 6$; $M >= +0.5569$]], [#text(size: 8.4pt)[LP particionado + `audit_standalone.py`]],
  ),
  caption: [Cuadro 1: Mapa epistemológico de los resultados del Artículo A según dominio y método de certificación.],
)

El manuscrito se organiza siguiendo estrictamente esta hoja de ruta. Las extensiones estructurales de economía descentralizada, fragmentación de firmas $N_f$, curvas institucionales en U bajo externalidades (Teorema 10) y crecimiento balanceado de tipo _Red Queen_ (Proposición 3\*) quedan reservadas a un trabajo complementario (_Artículo B_) para preservar la unidad metodológica entre afilamiento determinista, asintótica $A -> oo$ y certificación estocástica.

// ============================================================================
// SECCIÓN 2: LITERATURA RELACIONADA
// ============================================================================
= Literatura Relacionada

== Puntos de Skiba, Trampas de Pobreza y Dinámica No Convexa

Desde los trabajos seminales de Skiba (1978), Majumdar y Mitra (1982) y Dechert y Nishimura (1983), la existencia de funciones de producción localmente convexas o con costos fijos de adopción origina funciones valor no cóncavas, políticas óptimas discontinuas y un conjunto crítico de indiferencia (punto de Skiba) que separa cuencas de atracción hacia la extinción o hacia un estado estacionario próspero. Kamihigashi y Roy (2007), Akao, Kamihigashi y Nishimura (2011) y Akao, Ishii, Kamihigashi y Nishimura (2022) caracterizaron la existencia, continuidad y monotonía del capital crítico en entornos no cóncavos y no suaves; Wagener (2003) clasificó las bifurcaciones heteroclinas y globales del umbral de indiferencia en modelos dinámicos con puntos de inflexión; y Kraay y McKenzie (2014) contrastaron las predicciones empíricas de trampas de pobreza frente a dinámicas lentas de convergencia. A diferencia de estos estudios orientados a existencia o estática comparativa local, Milei y Reidel (2026) proponen certificar cotas globales de tiempo finito sobre las regiones $M_0$, $M$ y $H$ dentro de cajas compactas de incertidumbre paramétrica. Nuestro artículo afila analíticamente esas cotas y demuestra sus propiedades asintóticas y estocásticas rigurosas.

== Tecnologías CES y Trabajo Endógeno en Crecimiento

La sensibilidad de los umbrales de trampa respecto a la elasticidad de sustitución capital--trabajo ($sigma = 1\/(1 - rho) > 1$ o complementariedad bruta $rho < 0$, con $rho = -1$, $sigma = 1\/2$ en la parametrización CES armónica de MR) y la oferta laboral elástica cuenta con una vasta tradición en macroeconomía (Acemoglu, 2009). La literatura clásica suele fijar el insumo laboral $L = overline(L)$ para preservar tratabilidad analítica en las regiones asintóticas de baja escala. La Nota al pie 1 de MR plantea explícitamente en qué medida permitir la elección endógena del trabajo altera los umbrales de trampa cuando la productividad total de los factores $A$ crece sin cota. En la Sección 4 demostramos cómo el teorema asintótico $A -> oo$ colapsa la ventaja intramarginal del trabajo elástico a ritmo polilogarítmico mientras preserva el ordenamiento estricto para todo $A$ finito.

== Barreras de Bellman, Dualidad LP, Parada de Doob y Síntesis Certificada CEGIS

El respaldo formal de las barreras regionales descansa sobre tres pilares matemáticos clásicos: las desigualdades de variación y teoremas de envolvente sin diferenciabilidad bilateral de Milgrom y Segal (2002) (fundamentales para cerrar el régimen $beta theta > 1$), la teoría de viabilidad y funciones barrera/Lyapunov en sistemas discretos (Aubin, 1991), y la formulación dual mediante programación lineal continua de funciones sub-solución de Bellman (Hernández-Lerma y Lasserre, 1996). Para extender estas garantías deterministas al entorno con riesgo de ruina o transiciones de Markov utilizamos el teorema de parada opcional de Doob para supermartingalas detenidas (Doob, 1953; Williams, 1991).

En el plano algorítmico, nuestro motor se inscribe dentro de la literatura moderna de *síntesis certificada de funciones de Lyapunov y barrera mediante _CEGIS_ (_Counterexample-Guided Inductive Synthesis_)* bajo arquitectura desacoplada _Proposer--Verifier_ (Solar-Lezama, 2008; Ravanbakhsh y Sankaranarayanan, 2019; Abate et al., 2021). A diferencia de los enfoques de control neuronal puramente empíricos que dependen de muestreo probabilístico, empleamos aquí un _Proposer_ basado en programación lineal dispersa (HiGHS; Huangfu y Hall, 2018) con inserción adaptativa de nodos en los peores contraejemplos sobre splines continuos por tramos en escala logarítmica (_log-PWL_), mientras que el $100\%$ de la validez matemática descansa sobre un _Verifier_ determinista Branch-and-Bound 3D y 1D en espacio continuo cerrado con auditoría terminal de aritmética de intervalos de redondeo dirigido (Moore et al., 2009; Tucker, 2011). Esta separación vuelve inocua la complejidad de búsqueda del _Proposer_: una barrera sintética es un certificado puro y autocontenido cuya corrección puede re-auditarse en segundos.

// ============================================================================
// SECCIÓN 3: BARRERAS AFINES DE UN PASO Y REDUCCIÓN DE MR-TABLA 5
// ============================================================================
= Barreras Afines de Un Paso y Reducción Exacta de la Cota de Dos Pasos de MR

== Marco Paramétrico y Holgura de 2 Pasos

Conservamos íntegramente la calibración de referencia de MR (octubre de 2026): producción CES $F_A (K, L) = A [1\/2 (K^rho + L^rho)]^(theta\/rho)$ con $theta = 3\/2$, $rho = -1$ ($sigma = 1\/2$), forma equivalente $F_A (K, L) = A (2 K L \/ (K + L))^(3\/2)$, depreciación $delta = 0.08$ ($q = 1 - delta = 0.92$), y utilidad de período $u(c, L) = eta log c + (1 - eta) log(1 - L)$. La caja compacta de parámetros de MR es:
$ cal(P) = [A_-, A_+] times [q_-, q_+] times [beta_-, beta_+] times [eta_-, eta_+] = [0.749, 0.751] times [0.9199, 0.9201] times [0.9699, 0.9701] times [0.6999, 0.7001]. $
Para la región de tránsito $M = [b, h) = [0.10, 0.28)$ con techo de salida productivo $h = 0.28$, definimos el consumo máximo instantáneo de permanencia en $M$, $C_"max"^+ = q_+ h + F_(A_+) (h, 1) - b = 0.37495167$, y la cota superior de utilidad en $M$, $hat(R) = -0.996$. La función valor $V(K)$ verifica para todo $(K, theta_"par") in M times cal(P)$ y todo par factible $(K', L) in M times [0, 1)$ la desigualdad de permanencia $V(K) >= u(q K + F_A (K, L) - K', L) + beta V(K')$.

En su Sección 7.2 (Teorema 9 y Apéndice F.3), para evitar trabajar con pendientes no constantes de la barrera, los autores imponen una cota constante de bloque de $2$ pasos con incremento acumulado $Delta_2 = 0.2997$, obteniendo $B_0 = hat(R)\/(1 - beta_-) - Delta_2\/(1 - beta_-^2) = -38.144176$, lo que entrega un margen frente al testigo de MR-Tabla 4 $W_M (0.10) = -35.579855 > -35.58$ de apenas $2.564$, requiriendo $T = 46$ períodos consecutivos para garantizar la contradicción contra el techo $Psi^sharp (0.28)$ del Lema 12 / Apéndice F.3 (siendo MR-Tabla 5 la tabla de los $12$ subintervalos de salidas adversas).

== Lema 1, Teorema 9\* y Reducción Analítica a la Mitad ($46 -> 23$)

Demostramos que una simple función afín con pendiente analítica exacta $m_omega$ aprovecha paso a paso todo el gradiente mínimo disponible en $M$ sin requerir búsqueda numérica.

#thm_box("Lema", "1", [Cota inferior afín de la ganancia de permanencia en $M$])[
  Sea $m_omega = (eta_- q_-) \/ C_"max"^+ = 1.717123$. Para todo $K in M = [0.10, 0.28)$, todo $theta_"par" in cal(P)$ y toda política de permanencia factible $(K', L) in M times [0, 1)$ con consumo $c = q K + F_A (K, L) - K' > 0$:
  1. Acotando el consumo respecto de $C_"max"^+ = q_+ h + F_(A_+) (h, 1) - b = 0.37495167$ por $c <= (q_+ h + F_(A_+) (h, L) - b) - q_- (h - K) - (K' - b)$ y usando la concavidad de $eta log c$ sobre $(0, C_"max"^+]$, el retorno instantáneo satisface $u(c, L) <= hat(R) - m_omega (h - K) - (eta_- \/ C_"max"^+) (K' - b)$. En consecuencia, la función afín dependiente del estado $B_1 (K) = B_* - m_omega (h - K)$ con $B_* = (hat(R) - Delta_2) \/ (1 - beta)$ satisface la desigualdad de Bellman de un paso $u(c, L) + beta B_1 (K') <= B_1 (K)$ en todo $M times M$.
  2. La holgura por distancia al borde superior $h$ respecto del máximo global $hat(R) = -0.996$ satisface la cota exacta $Delta_2^"exact" = eta_- beta_- q_- (h - b) \/ C_"max"^+ = 0.2997787 > Delta_2 = 0.2997$, alcanzando uniformemente en $cal(P)$:
     $ B_1 (K) <= B_* = -43.0465116, #h(12pt) B_1 (b) <= -43.355594, $
     con margen estado a estado $W_M (K) - B_1 (K) >= W_M (b) - B_1 (b) > 7.775594$ (y uniforme $W_M (K) - B_* > 7.4665$).
]

#proof_block(title: "Demostración del Lema 1")[
  Para cualquier transición $(K, K') in M times M$, sea $L in [0, 1)$ el esfuerzo laboral con consumo $c_0 = q K + F_A (K, L) - K' > 0$, y sea $c_1 = q_+ h + F_(A_+) (h, L) - b <= C_"max"^+$. Como el trío $(h, b, L)$ es factible en $(h, b)$ y el término de ocio $(1 - eta) log(1 - L)$ se cancela idénticamente entre ambas evaluaciones, la concavidad del logaritmo ($log(c_1 \/ c_0) >= (c_1 - c_0) \/ c_1$) junto con $F_(A_+) (h, L) >= F_A (K, L)$ implican:
  $ u_"sup" (h, b) - u(c_0, L) >= eta log(c_1 \/ c_0) >= eta (c_1 - c_0) / c_1 >= (eta_-) / C_"max"^+ [q_- (h - K) + (K' - b)]. $
  Acotando $u_"sup" (h, b) <= hat(R)$ se obtiene la primera desigualdad del enunciado. Sustituyendo ahora $B_1 (K') = B_* - m_omega (h - K')$:
  $ u(c_0, L) + beta B_1 (K') <= hat(R) + beta B_* - m_omega (h - K) - (eta_-) / C_"max"^+ [(K' - b) + beta q_- (h - K')]. $
  Dado que $K' in [b, h)$ y $beta q_- < 1$, la combinación lineal en $K'$ cumple $(K' - b) + beta q_- (h - K') = (1 - beta q_-)(K' - b) + beta q_- (h - b) >= beta_- q_- (h - b)$, por lo que el último corchete queda acotado inferiormente por $Delta_2^"exact" = 0.2997787 > Delta_2 = 0.2997$. Por definición $hat(R) - Delta_2 + beta B_* = B_*$, concluyendo $u(c_0, L) + beta B_1 (K') <= B_1 (K)$ para todo $(K, K') in M^2$. En la caja $cal(P)$, $hat(R) - Delta_2 = -1.2957 < 0$ y $beta >= beta_- = 0.9699$ rinden $B_* <= -1.2957 \/ 0.0301 = -43.0465116$, mientras que $m_omega = (0.6999 times 0.9199) \/ 0.37495167 = 1.717123$ entrega $B_1 (b) <= -43.0465116 - 1.717123(0.18) = -43.355594$. Finalmente, como el consumo en el primer paso del testigo $c_M (K) = q_- K + F_(A_-) (K, 0.68) - 0.135$ cumple $0 < c_M (K) < min{1 - 0.68, C_"max"^+}$, la rama activa del mínimo en $eta$ lleva $eta_+$ (siendo $eta_- <= eta_+$ cota inferior válida) y $partial F_(A_-) \/ partial K > 0$, por lo que la derivada del piso del testigo verifica $W'_M (K) >= eta_- [q_- + partial F_(A_-) \/ partial K (K, 0.68)] \/ c_M (K) > m_omega = B'_1 (K)$ en todo $M$. Por lo tanto, $W_M (K) - B_1 (K)$ es estrictamente creciente y alcanza su ínfimo en $K = b = 0.10$: $inf_M (W_M - B_1) = W_M (0.10) - B_1 (0.10) = -35.57985494 - (-43.355594) > 7.775594$.
]

#thm_box("Teorema", "9*", [Afilamiento analítico de un paso: reducción de $tau_H <= 46$ a $tau_H <= 23$])[
  Sea la barrera afín de un paso sobre $M = [0.10, 0.28)$ dada por:
  $ B_1 (K) = B_* - m_omega (h - K), #h(12pt) B_* = -43.0465116, #h(12pt) m_omega = (eta_- q_-) / C_"max"^+ = 1.717123. $
  Entonces $B_1 (K)$ es una sub-barrera global de permanencia certificada para toda trayectoria que permanece en $M$ bajo cualquier parámetro en $cal(P)$, con extremos $B_1 (0.10) = -43.355594$ y $B_1 (0.28) = -43.046512$. Comparada frente al testigo $W_M (0.10) = -35.57985494$ de MR-Tabla 4 y al techo analítico $Psi^sharp (0.28)$ del Lema 12 / Apéndice F.3 de MR:
  - El margen en el borde inferior aumenta desde $2.564$ hasta $W_M (0.10) - B_1 (0.10) = 7.775594$ estado a estado (o $7.4665$ uniforme frente a $B_*$).
  - El plazo máximo de permanencia consecutiva en $M$ antes de alcanzar o superar $h = 0.28$ cae exactamente a la mitad: de *$tau_H <= 46$* a *$tau_H <= 23$* (con holgura positiva verificada en $T = 23$ igual a $+0.205614$, y $tau_H <= 24$ bajo cota uniforme independiente de $K_0$). Si $K_0 in [0.10, 0.105]$, vale además $3 <= tau_H <= 23$.
]

#proof_block(title: "Demostración del Teorema 9*")[
  Consideremos cualquier trayectoria factible $x_0 -> x_1 -> dots -> x_T$ que permanezca en $M$ durante $T >= 1$ transiciones consecutivas ($x_t in M$ para $0 <= t <= T$), seguida de una continuación óptima desde $x_T$. Iterando la desigualdad de un paso del Lema 1 ($u(c_t, L_t) <= B_1 (x_t) - beta B_1 (x_(t+1))$) sobre $t = 0, dots, T - 1$ y acotando la continuación en $t = T$ por $V(x_T) <= Psi^sharp (x_T)$, el bienestar total $J_(x_0) (pi)$ cumple:
  $ J_(x_0) (pi) <= B_1 (x_0) + beta^T [Psi^sharp (x_T) - B_1 (x_T)]. $
  En $x in [0.10, 0.28)$, la derivada de $Psi^sharp (x) = 0.4 x - 5 x^(-1\/2) - 18.5 - 10\/301$ satisface $(Psi^sharp)'(x) = 0.4 + 2.5 x^(-3\/2) >= 0.4 + 2.5 (0.28)^(-3\/2) = 17.272 > 2 > m_omega = B'_1 (x)$. Por lo tanto, $Psi^sharp (x_T) - B_1 (x_T)$ es estrictamente creciente en $x_T in [b, h)$ y alcanza su supremo en $x_T -> h^-$, acotado por $Psi^sharp (h) - B_* (beta) < -27.83 - B_* (beta)$ (MR, pág. 59). Sea $B_*^max := B_* (beta_-) = -43.0465116$, de modo que $B_* (beta) <= B_*^max$ en $[beta_-, beta_+]$. Reagrupando con $1 - beta^T > 0$ y $-27.83 - B_*^max > 0$:
  $ J_(x_0) (pi) <= (1 - beta^T) B_* (beta) - m_omega (h - x_0) + beta^T (-27.83) <= B_*^max - m_omega (h - x_0) + beta_+^T (-27.83 - B_*^max). $
  En la _cota uniforme_ ($T = 24$, acotando $-m_omega (h - x_0) <= 0$), resulta $J_(x_0) (pi) <= -43.0465116 + (0.9701)^24 (15.2165116) = -35.70287 < -35.58 <= W_M (x_0)$. En la _cota estado a estado_ ($T = 23$), como $W_M (x_0) - [B_*^max - m_omega (h - x_0)]$ es estrictamente creciente en $x_0 in [b, h)$ por el Lema 1, su mínimo se alcanza en $x_0 = b = 0.10$:
  $ W_M (x_0) - J_(x_0) (pi) &>= [W_M (0.10) - B_1 (0.10)] - beta_+^23 (-27.83 - B_*^max) \
  &= 7.775594 - (0.9701)^23 (15.2165116) = +0.205614 > 0. $
  En consecuencia, ningún óptimo puede permanecer en $M$ durante $23$ períodos consecutivos ($tau_H <= 23$). Finalmente, la cota inferior $tau_H >= 3$ en $[0.10, 0.105]$ se mantiene intacta desde la tecnología de MR al verificarse dos pasos por debajo de $0.28$.
]

== Proposición 1\*, Prueba Uniforme en $M_0$ y Cascada Completa hacia CEGIS-PWL ($23 -> 9 -> 5 -> 4$)

Examinamos ahora la región previa de arranque $M_0 = [0.05, 0.10)$ bajo la calibración de MR.

#thm_box("Proposición", "1*", [Condición analítica en $M_0$ y testigo afilado con plazo $tau_(.1) <= 9$])[
  1. *(Condición exacta de monotonía en $eta$ y cota base $tau_(.1) <= 10$):* En $M_0 = [0.05, 0.10)$ con ocio positivo $L$, la derivada parcial de la utilidad instantánea respecto de $eta$ es $partial u \/ partial eta = log(c \/ (1 - L))$, por lo que la evaluación adversa en $(A_-, q_-, eta_+)$ requiere estrictamente *$c < 1 - L = 0.25$*. En los tres pasos del testigo de MR sobre $M_0$ ($0.05 -> 0.065 -> 0.0845 -> 0.100$ con $L = 0.75$), los consumos resultantes $[0.002495, 0.006286, 0.022068]$ satisfacen todos $c < 0.25$, arrojando $tau_(.1) <= 10$ ($J(10; 0.05) = -43.899678 < -43.844826 = W_(M_0) (0.05)$).
  2. *(Testigo afilado y extensión uniforme a todo $M_0$ con $tau_(.1) <= 9$):* Sustituyendo la senda anterior por la trayectoria suavizada de tres pasos $(K_0 -> 0.0595 -> 0.0755 -> 0.100)$ con esfuerzo $(0.45, 0.50, 0.60)$, cuyas utilidades de etapa en $(A_-, q_-, eta_+)$ son $[-3.681867, -3.888538, -3.828711]$ y cuyo piso vale $W_(M_0)^"sharp" (0.05) = -43.540132$, y acoplándola al techo de continuación certificado CEGIS-LP $Psi(0.10) = -35.166686$, el prefijo de $T = 9$ pasos cumple $J(9; 0.05) = -44.065405$, entregando holgura estrictamente positiva de $+0.525273$ (frente a la cola de MR-Tabla 4) y $+0.559826$ (frente al testigo CEGIS $W(0.10)$) uniformemente para todo $K_0 in [0.05, 0.10)$. En consecuencia, se certifica *$tau_(.1) <= 9$* en toda $M_0$.
]

#proof_block(title: "Demostración de la Proposición 1*")[
  Aplicando el Lema 1 a $M_0 = [b_0, h_0) = [0.05, 0.10)$, la maximización sobre $L in [0, 1)$ rinde $C_"max,0"^+ = q_+ (0.10) + F_(A_+) (0.10, 1) - 0.05 = 0.100233$, $Delta_0^"exact" = (eta_- beta_- q_- dot 0.05) \/ C_"max,0"^+ = 0.311503 > Delta_0 = 0.3115$, $hat(R)_0 = -1.827$ y $B_*^((0), max) = (-1.827 - 0.3115) \/ (1 - beta_-) = -71.046512$ (con $B^((0)) (K_0) = B_*^((0)) - (eta_- q_-) \/ C_"max,0"^+ dot (0.10 - K_0)$ y pendiente constante $(B^((0)))'(K_0) = 6.4234$). Para el testigo afilado $W_(M_0)^"sharp" (K_0)$ con liquidación temporal en un paso ($K_0 -> 0.0595$), el consumo de primera etapa $c_0^"sharp" (K_0) = q_- K_0 + F_(A_-) (K_0, 0.45) - 0.0595$ satisface $c_0^"sharp" (K_0) <= c_0^"sharp" (0.10^-) = 0.0822 < 1 - 0.45 = 0.55$ y $c_0^"sharp" (K_0) < C_"max,0"^+ = 0.100233$. Dado que $c_0^"sharp" < 1 - L$, la rama activa lleva $eta_+$, por lo que $eta_-$ proporciona la cota inferior de derivada:
  $ (W_(M_0)^"sharp")'(K_0) >= eta_- (q_- + F_(A,K)^(-) (K_0, 0.45)) / (c_0^"sharp" (K_0)) > (eta_- q_-) / C_"max,0"^+ = (B^((0)))'(K_0) = 6.4234 #h(8pt) forall K_0 in [0.05, 0.10), $
  donde $F_(A,K)^(-)$ denota $(partial F_(A_-)) / (partial K)$. Asimismo, sobre el techo CEGIS-LP $Psi$ del Caso 1, la auditoría exacta por intervalos `Decimal` de 50 dígitos sobre $[0.05, 0.10]$ certifica $inf_(x in [0.05, 0.10)) Psi'(x) >= 91.23 > 6.4234 = (B^((0)))'(x)$, por lo que $Psi(x_9) - B^((0)) (x_9)$ es también estrictamente creciente en todo $M_0$ y alcanza su supremo exactamente en $x_9 -> 0.10^-$. En consecuencia, $W_(M_0)^"sharp" (K_0) - B^((0)) (K_0; beta_-)$ es estrictamente creciente en $[0.05, 0.10)$ y alcanza su ínfimo exactamente en el borde izquierdo $K_0 = 0.05$. Reagrupando como en el Teorema 9\* con $Psi(0.10) = -35.166686$:
  $ W_(M_0)^"sharp" (K_0) - J(9; K_0) >= [W_(M_0)^"sharp" (0.05) - B^((0)) (0.05)] - beta_+^9 [Psi(0.10) - B_*^((0), max)] = +0.525273 > 0, $
  garantizando $tau_(.1) <= 9$ uniformemente sobre todo $M_0 = [0.05, 0.10)$ (combinado con la ausencia de salidas adversas por debajo de $0.05$ del Teorema 8 de MR).
]

Al combinar el Teorema 9\* con las herramientas computacionales de la Sección 5 obtenemos la cascada completa de holgura sobre $M = [0.10, 0.28)$ (ilustrada en la Figura 1):
- *Bloques de $2$ pasos de MR (Sec. 7.2 / Ap. F.3):* $B_0 = -38.144176 ==>$ *$tau_H <= 46$* (holgura $>= 2.564$).
- *Barrera afín analítica cerrada de $1$ paso ($B_1$, Teorema 9\*):* $[-43.356, -43.047] ==>$ *$tau_H <= 23$* (holgura $7.776$).
- *Barrera adaptativa CEGIS-LP ($B_theta$, Caso 1, $57$ nodos / $22$ compacto):* $[-56.6905, -52.3524] ==>$ *$T_theta = 9$* frente a MR-Tabla 4 (holgura $19.0600$) y *$T_"full" = 5$* al usar la tripleta completa CEGIS-LP $(Psi, W, B_theta)$ (holgura $21.0857$, techo $24.2013$), comprimiéndose ulteriormente a *$T_"ns" (cal(P)) = 5$* y *$T_"ns" (theta_0) = 4 = tau_H^"VFI"$* con la cadena no estacionaria de la Sección 5.
- *Límites inferiores verdaderos:* La programación dinámica restringida exacta sobre $M$ con $Psi^sharp$ y $W_M$ arroja *$tau_H^"DP" = 9$* (brecha en $T = 8$: $+0.028144 > 0$; en $T = 9$: $-0.556742 < 0$), casi saturada por la barrera óptima regional analítica $B_"opt"$ ($[-56.795, -52.458]$), mientras que la solución por iteración de la función valor (VFI) en el centro $A = 0.75, beta = 0.97$ ($V(0.10) = -35.596111$) escapa de todo $M$ en *$tau_H^"VFI" = 4$* períodos.

#v(0.3em)
#figure(
  image("fig1_barrier_es.svg", width: 100%),
  caption: [Figura 1: (a) Comparación de las barreras analíticas ($B_0, B_1$) y CEGIS-LP determinista ($B_theta$, $57$ nodos; versión compacta $22$ nodos equivalente) frente a $W_M$ y $Psi^sharp$ sobre $M = [0.10, 0.28)$. (b) Cascada completa de plazos desde $tau_H <= 46$ hasta $T_"full" <= 5$ y $T_"ns" (theta_0) = 4 = tau_H^"VFI"$.],
)

== Proposición 1\*\* y Certificación Continua de Salidas Adversas (Tabla 2)

Para completar el certificado determinista de la Sección 3 sin muestreo discreto, verificamos las cotas superiores globales de salida $E^+(K, a; l_0)$ que aparecen cuando el estado elegido $K'$ abandona una subregión por debajo de $a$ ($a = b = 0.10$ en $M$, $a = h = 0.28$ en $H_1 = [0.28, 0.80)$).

#thm_box("Proposición", "1**", [Monotonía del Wronskiano y certificación de intervalos en salidas adversas])[
  Para todo par de umbral $(a, l_0)$ con consumo excedente $c_"sup" (K; a, l_0) = S(K) - a$, donde $S(K) = q_+ K + F_(A_+) (K, l_0) + (1 - l_0) t(K)$ y $t(K) = partial F_(A_+) \/ partial L (K, l_0) = 1.5 A_+ dot 2^(3\/2) K^(5\/2) l_0^(1\/2) (K + l_0)^(-5\/2)$, la función envolvente exacta de utilidad inmediata condicionada a no sobrepasar $a$ admite la forma cerrada autocontenida:
  $ E^+(K, a; l_0) = max_(eta in {eta_-, eta_+}) { eta log (c_"sup" (K; a, l_0) - t(K) omega^*(K, eta)) + (1 - eta) log omega^*(K, eta) }, $
  donde $omega^*(K, eta) = min{1, (1 - eta) c_"sup" (K; a, l_0) \/ t(K)}$ es la demanda óptima de ocio acotada por el límite unitario. En todo intervalo donde $omega^* < 1$, la identidad de la envolvente rinde exactamente:
  $ (d E^+) / (d K) = (S'(K)) / (S(K) - a) - (1 - eta) (5 l_0) / (2 K (K + l_0)). $
  Definida la ventaja puntual del testigo $Delta_X (K) := W_X (K) - [E^+(K, a; l_0) + beta_- Psi^sharp (a)]$ (nótese $beta_-$ al ser $Psi^sharp (a) < 0$) y el cociente $R_X (K) := (S(K) - a) \/ c_X (K)$, evaluando el Wronskiano continuo $Q_X (K) = S'(K) c_X (K) - c'_X (K)(S(K) - a)$ por aritmética de intervalos `Decimal` de $50$ dígitos sobre $M$ ($l_0 = 0.44$) y $H_1$ ($l_0 = 0.60, l_0 = 0.57$), se certifica $Q_M <= [-0.06341, -0.04375] < 0$, $Q_(H_1) <= [-0.18976, -0.13124] < 0$, $Delta'_M >= +0.0723 > 0$, $Delta'_(H_1) >= +0.0095 > 0$, y concavidad global $Delta''_M <= -2.5107 < 0$, $Delta''_(H_1) <= -0.1889 < 0$, alcanzando el mínimo exactamente en el borde izquierdo con márgenes $+0.094717$ en $K = 0.10$ y $+0.057148$ en $K = 0.28$.
]

#proof_block(title: "Demostración de la Proposición 1**")[
  Sea $X in {M, H_1}$ con testigo $W_X (K) = u_"worst" (c_X (K), l_X) + beta_+ T_X$, consumo $c_X (K) = q_- K + F_(A_-) (K, l_X) - s_X > 0$, y parámetro tangente $l_0 >= sup(X)\/2$ ($0.44 >= 0.14$ en $M$ y $0.57 >= 0.40$ en $H_1$), condición suficiente para la dominancia global de la tangente en $L in [0, 1)$. Mediante intervalos `Decimal` de 50 dígitos se verifica primero interioridad estricta del ocio óptimo de la envolvente en toda la región ($omega^*(K) in [0.5662, 0.6808] < 1$ en $M$ y $omega^*(K) in [0.4301, 0.5427] < 1$ en $H_1$), así como la dominancia estricta en la rama inferior de salida $s = 0$ de (F.20) de MR ($W_X (K) - [E^+(K, 0; l_0) + beta_- Psi^sharp (0.05)] > 0$ uniformemente en $M$ y $H_1$). Como $t'(K) \/ t(K) = 5 l_0 \/ (2 K (K + l_0)) > 0$ y $(t'\/t)'(K) = -5 l_0 (2 K + l_0) \/ (2 K^2 (K + l_0)^2) < 0$, diferenciando cada rama de $W_X$ y $E^+$ mediante la envolvente en $omega^*(K) < 1$ se obtiene en todo punto suave (y para ambas derivadas laterales en los eventuales quiebres):
  $ Delta'_X (K) >= (eta_- c'_X (K) R_X (K) - S'(K)) / (S(K) - a) + (1 - eta_+) (5 l_0) / (2 K (K + l_0)), #h(10pt) R_X (K) := (S(K) - a) / (c_X (K)) > 1. $
  La derivada del cociente verifica $R'_X (K) = Q_X (K) \/ c_X (K)^2$ con Wronskiano $Q_X (K) := S'(K) c_X (K) - c'_X (K)(S(K) - a)$, cuya derivada $Q'_X (K) = S''(K) c_X (K) - c''_X (K)(S(K) - a)$ cancela el término $S' c'_X$. Acotando $|Q'_X|$ en cada subintervalo $[k_L, k_R]$ mediante los extremos y los picos únicos de $|F_(A, K thin K)|$ y $|t''|$, la forma centrada arroja $Q_M <= -0.04375 < 0$ en los $4$ subintervalos de $M$ y $Q_(H_1) <= -0.13124 < 0$ en los $6$ subintervalos de $H_1$. Así $R_X (K)$ es estrictamente decreciente en todo $X$, rindiendo $inf_M Delta'_M >= +0.0723 > 0$ e $inf_(H_1) Delta'_(H_1) >= +0.0095 > 0$ (sin mínimos interiores). Además, en las regiones suaves:
  $ Delta''_X (K) <= ((S')^2 - eta_- (c'_X R_X)^2) / ((S - a)^2) + (eta_plus.minus c''_X) / c_X - (S'') / (S - a) + (1 - eta_+) (t' / t)'(K), $
  evaluando $eta c''_X \/ c_X$ en $eta_+$ cuando $c''_X > 0$ (en $[0.10, l_M\/4 = 0.17)$) y en $eta_-$ cuando $c''_X <= 0$. La partición en $8$ subintervalos de $M$ y $10$ de $H_1$ certifica $Delta''_M <= -2.5107 < 0$ y $Delta''_(H_1) <= -0.1889 < 0$. Los dos únicos quiebres en $H_1$ —en $k_W = 0.406819$ donde $c_(H_1) (K) = 1 - l_H$ ($W'_(H_1)$ cae de $3.954006$ a $3.952877$) y en $k_E = 0.573570$ donde $(-E^+)'$ cae de $-1.652310$ a $-1.652744$— son ambos quiebres hacia abajo que preservan la concavidad global de $Delta_X$. Por ende, $Delta'_X$ alcanza su ínfimo en el borde derecho ($Delta'_M (0.28^-) = +0.502666$, $Delta'_(H_1) (0.80^-) = +0.100489$) y $Delta_X$ alcanza su mínimo en el borde izquierdo: $+0.094717$ en $K = 0.10$ ($+0.062495$ frente al techo analítico $Psi$ de MR sin desplazamiento) y $+0.057148$ en $K = 0.28$ con $l_0 = 0.57$ ($+0.024926$ frente a $Psi$ sin desplazamiento de MR).
]

La Tabla 2 resume la auditoría cuantitativa de intervalos de la Proposición 1\*\* en los extremos regionales comparando frente al techo analítico con desplazamiento $Psi^sharp$ y al techo analítico sin desplazamiento $Psi$ de MR (frente a la súper-barrera CEGIS-LP $Psi$ del Caso 1/Caso 2 en $p = 0\%$, los márgenes ascienden a $+0.787$ en $M$ y $+0.236$ en $H_1$).

#figure(
  table(
    columns: (1.2fr, 1.0fr, 1.3fr, 1.3fr, 1.4fr),
    inset: 6pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.8pt)[Región / Punto],
      text(fill: white, weight: "bold", size: 8.8pt)[Política $l_0$],
      text(fill: white, weight: "bold", size: 8.8pt)[Wronskiano $sup Q$],
      text(fill: white, weight: "bold", size: 8.8pt)[Cota $inf Delta'$],
      text(fill: white, weight: "bold", size: 8.8pt)[Margen $W - E^+ - beta_- Psi$],
    ),
    [$M = [0.10, 0.28)$], [$0.44$], [$-0.04375 < 0$], [$+0.0723 > 0$], [$+0.0947$ ($Psi^sharp$) / $+0.0625$ ($Psi$ MR)],
    [$H_1 = [0.28, 0.80)$], [$0.60$], [$-0.12362 < 0$], [$+0.0118 > 0$], [$+0.0561$ ($Psi^sharp$)],
    [$H_1 = [0.28, 0.80)$], [$0.57$], [$-0.13124 < 0$], [$+0.0095 > 0$], [$+0.0571$ ($Psi^sharp$) / $+0.0249$ ($Psi$ MR)],
  ),
  caption: [Tabla 2: Auditoría por intervalos (50 dígitos) de las condiciones del Wronskiano y márgenes de salida adversa frente a los techos analíticos $Psi^sharp$ y $Psi$ de MR.],
)

// ============================================================================
// SECCIÓN 4: EQUIVALENCIA ASINTÓTICA (NOTA AL PIE 1)
// ============================================================================
= Equivalencia Asintótica bajo Escalamiento ($A -> oo$)

La Nota al pie 1 de Milei y Reidel (octubre de 2026) deja abierto si el modelo completo con trabajo endógeno $L_t in [0, 1)$ exhibe la misma ley de potencia asintótica que el modelo simplificado con trabajo fijo en $overline(L) = 1$ cuando $A -> oo$. Denotemos $S_A$ el umbral de Skiba bajo trabajo endógeno (único bajo $beta theta > 1$), y $S_A^"fix" (overline(L))$ el umbral análogo bajo oferta fija $L_t equiv overline(L)$. Definimos $d = -rho > 0$ y el exponente homogéneo de retorno decreciente en escala $r = theta - 1 in (0, 1)$ (con $theta = 3\/2$, $r = 1\/2$ en la parametrización CES armónica $d = 1$), $c_K = w^(theta\/rho) = 2^(3\/2) approx 2.828427$, $nu = (1 - eta)\/eta$, y el capital estacionario de referencia $K_"ss" (A)$ donde $F_(A,K) (K_"ss", 1) = D = 1\/beta - q$.

== Teorema 3\*, Parte 1 y Corolario 2\* ($beta theta > 1$)

#thm_box("Teorema", "3*", [Parte 1: Convergencia uniforme hacia la ley de potencia asintótica])[
  Fijemos los parámetros primitivos distintos de $A$ en la región paciente con $d = -rho > 0$, $r = theta - 1 in (0, 1)$ y $beta theta > 1$. Sea $c_K = lim_(k -> 0^+) F_1 (k, 1)\/k^theta = w^(theta\/rho) = 2^(3\/2)$. Reescalando $K_t = A^(-1\/r) k_t$ y $C_t = A^(-1\/r) c_t$ con $k_t, c_t = Theta(1)$, a lo largo de toda acción óptima interior la oferta laboral y la razón capital--trabajo obedecen:
  $ L_t = Theta(A^(-d\/(r(1+d)))) -> 0, #h(12pt) K_t / L_t = Theta(A^(-1\/(r(1+d)))) -> 0 #h(8pt) (A -> oo). $
  En consecuencia, la desutilidad del ocio se anula como $(1 - eta)|log(1 - L_t)| = O(A^(-d\/(r(1+d)))) -> 0$ y ambos umbrales críticos normalizados convergen al límite físico de reposición común $(delta\/c_K)^(1\/r)$ para todo $overline(L) in (0, 1]$:
  $ lim_(A -> oo) A^(1\/r) S_A^"fix" (overline(L)) = lim_(A -> oo) A^(1\/r) S_A = (delta / c_K)^(1\/r), #h(12pt) lim_(A -> oo) (S_A) / (S_A^"fix" (overline(L))) = 1. $
  En la calibración estándar ($theta = 3\/2$, $r = 1\/2$, $delta = 0.08$, $c_K = 2^(3\/2)$), este límite es exactamente $(delta\/c_K)^2 = 0.000800$.
]

#proof_block(title: "Demostración del Teorema 3*, Parte 1")[
  Con $K = A^(-1\/r) k$ y $C = A^(-1\/r) c$ ($r = theta - 1$, $rho = -d < 0$), el producto normalizado vale:
  $ f_A (k, L) := A^(1\/r) F_A (A^(-1\/r) k, L) = c_K k^theta [1 + c_w (k / (A^(1\/r) L))^d]^(-theta\/d), #h(10pt) c_w = (1 - w) / w. $
  Con trabajo fijo $L equiv overline(L) in (0, 1]$, $(A^(1\/r) overline(L))^(-d) = O(A^(-d\/r)) -> 0$ y $f_A (k, overline(L)) -> c_K k^theta$. Con trabajo endógeno, multiplicando la condición de primer orden $F_(A,L) (K, L) = nu C \/ (1 - L)$ por $A^(1\/r)$ resulta:
  $ theta c_K c_w k^(theta + d) A^(-d\/r) L^(-1 - d) [1 + c_w ((A^(1\/r) L) / k)^(-d)]^(-1 - theta\/d) = (nu c) / (1 - L), $
  lo cual fuerza $L = [theta c_K c_w k^(theta + d) \/ (nu c)]^(1\/(1+d)) A^(-d\/(r(1+d))) (1 + o(1)) -> 0$ y $K\/L = Theta(A^(-1\/(r(1+d)))) -> 0$. Para demostrar la convergencia de las fronteras mismas, fijemos cualquier $k_0 > (delta\/c_K)^(1\/r)$, sea $K_0 = A^(-1\/r) k_0$, y construyamos una expansión factible en tres fases manteniendo trabajo constante $L_0$ ($L_0 = 3\/4$ en el problema endógeno; $L_0 = 1$ o $overline(L)$ en trabajo fijo):
  - _Fase I (escape del cuello de botella):_ Eligiendo $epsilon.alt_1 in (0, 1)$ con $c_K (1 - epsilon.alt_1) k_0^r > delta$ y un umbral macroscópico fijo $K_"esc" > 0$ suficientemente pequeño para tener $f_A (k, L_0) >= c_K (1 - epsilon.alt_1\/2) k^theta$ en $K_t <= K_"esc"$, consumir la mitad del excedente neto sobre $k_t$ alcanza en $T_1 (k_0) < oo$ pasos (independientes de $A$) un nivel $k_(T_1) >= k_1 := max{2, (2\/[c_K (1 - epsilon.alt_1\/2)])^(1\/(theta - tilde(theta)))}$ donde $tilde(theta) in (beta^(-1), theta)$ existe por $beta theta > 1$.
  - _Fase II (crecimiento superexponencial):_ Ahorrando $K_(t+1) = [q K_t + F_A (K_t, L_0)]\/2$, por inducción $k_(t+1) >= k_t^(tilde(theta)) >= 2^(tilde(theta)^t)$, superando $K_"esc"$ en a lo sumo $J(A) <= (log log A)\/(log tilde(theta)) + O(1)$ pasos (en el último salto se ahorra exactamente $K_(T_1+J+1) = K_"esc"$).
  - _Fase III (meseta macroscópica):_ Mantener $K_"esc"$ rinde consumo $A F_1 (K_"esc", L_0) - delta K_"esc" = Omega(A)$ y utilidad descontada al menos $beta^(T_1+J+1) eta\/(1 - beta) dot log A - O(1)$.
  Como durante las Fases I--II el consumo $C_t = Omega(A^(-1\/r))$ aporta utilidad acumulada al menos $-(1 - beta^(T_1+J+1)) eta\/(r(1 - beta)) dot log A - O(1)$, mientras que por la cota de recursos del Lema 9 de MR toda senda confinada en $(0, K_0]$ (incluido cualquier óptimo que se extingue) tiene valor acotado por $-eta\/(r(1 - beta)) dot log A + O(1)$, el término dominante $-eta\/(r(1 - beta)) dot log A$ se cancela exactamente y el excedente neto escala al menos como:
  $ beta^(T_1 + J(A) + 1) (theta eta) / (r(1 - beta)) log A - O(1) >= c_1 (log A)^(1 - |log beta| \/ log tilde(theta)) - O(1) -> +oo, $
  pues $beta tilde(theta) > 1 ==> 1 - |log beta| \/ log tilde(theta) > 0$. Por contradicción, ningún óptimo puede extinguirse desde $K_0 = A^(-1\/r) k_0$ para $A$ grande, probando $limsup_(A -> oo) A^(1\/r) S_A <= (delta\/c_K)^(1\/r)$; combinando con la cota física inferior $A^(1\/r) kappa_A -> (delta\/c_K)^(1\/r)$ queda demostrado el límite común.
]

#thm_box("Corolario", "2*", [Extensión y unicidad en el régimen de paciencia débil $beta theta > 1$])[
  Supóngase únicamente $beta in (0, 1)$ y *$beta theta > 1$*, sin exigir la condición más fuerte (2.3) de MR ($beta [q + theta delta] > 1$). Definidos los umbrales generales $S_A^- := inf{K_0 > 0 : "algún óptimo desde " K_0 " sobrevive"}$ y $S_A^+ := sup{K_0 > 0 : "algún óptimo desde " K_0 " se extingue"}$, se cumple $kappa_A <= S_A^- <= S_A^+$, ambos convergen al mismo límite físico $(delta\/c_K)^(1\/r)$ cuando $A -> oo$, y para todo $A$ suficientemente grande existe un único punto de Skiba $S_A^- = S_A^+ = S_A$. Verificamos numéricamente el Corolario en $beta = 0.90$ ($beta theta = 1.35 > 1$, $(D\/c_K)^2 = 0.004565$): entre $A = 1.5$ y $A = 10^8$, la razón $S_A \/ S_A^"fix" (1)$ cae monótonamente de $1.05629$ a $1.00191$ ($A^2 S_A^"fix" (1) = 0.001714 < A^2 S_A = 0.001717 < 0.004565$).
]

#proof_block(title: "Demostración del Corolario 2*")[
  Para todo $beta in (0, 1)$, la cota tecnológica $F_A (K, 1) < A (1 - w)^(theta\/rho)$ confina las trayectorias factibles desde cualquier $K_0 > 0$ al compacto $[0, K_"max" (K_0, A)]$, asegurando existencia de óptimos y continuidad de $V_A (K)$ (Lema 1 de MR, independiente de (2.3)). Para trasladar el argumento de cruce único al régimen $beta theta > 1$ sin (2.3) verificamos cuatro eslabones explícitos:
  1. *(Ancla productiva en $b$ y supermodularidad local en $(0, b]$):* Fijando $b_A := (delta\/c_K + 1)^(1\/r) A^(-1\/r)$ (de orden $Theta(A^(-1\/r))$), para todo $A$ suficientemente grande se cumplen las cotas locales de cruce $L\/K > c$ sobre $(0, b_A]$ que garantizan tanto la sub-optimalidad del trabajo nulo como la positividad de la derivada cruzada $r_("red", K s) > 0$ (Lema 5 de MR, cuya algebra CES en Apéndice A.5 no utiliza (2.3)). Paralelamente, la expansión en tres fases del Teorema 3\* desde $b_A$ (válida siempre que $beta theta > 1$) entrega un umbral productivo por encima de toda extinción posible en $(0, b_A]$, estableciendo $S_A^+ <= b_A$ y monotonicidad temporal de todo óptimo dentro de $(0, b_A]$: toda senda óptima que se extingue desde $K_0 <= b_A$ permanece confinada en $(0, K_0]$.
  2. *(Exclusión de óptimos estacionarios cuando $E = D - theta delta >= 0$):* En el régimen de MR ($E < 0$), el Lema 6 descarta raíces estacionarias interiores en $(0, b_A]$; cuando $E >= 0$ (como ocurre en $beta = 0.90$, donde $E = +0.0089 > 0$), la ecuación de Euler sí admite un candidato estacionario interior $K_"stat" (A) = (D \/ (theta c_K))^(1\/r) A^(-1\/r) (1 + o(1))$. Distinguimos dos subcasos:
     - Si $E = D - theta delta > 0$, entonces $D\/theta > delta$, de modo que $(D\/(theta c_K))^(1\/r) > (delta\/c_K)^(1\/r)$ y existe $epsilon.alt_2 > 0$ independiente de $A$ tal que $K_"stat" (A) > [(delta\/c_K)^(1\/r) + epsilon.alt_2] A^(-1\/r)$ para todo $A$ suficientemente grande; aplicando la construcción en tres fases del Teorema 3\* desde $K_0 = K_"stat" (A)$, la ganancia de escape respecto de la senda estacionaria diverge a $+oo$ sobre el término base $-eta\/(r(1 - beta)) log A + O(1)$.
     - En el caso borde $E = 0$ ($D = theta delta$), aunque $A^(1\/r) K_"stat" (A) = (delta\/c_K)^(1\/r) + Theta(A^(-d\/r))$, combinando las condiciones estacionarias $F_(A, K) = theta delta$ y $F_(A, L) = nu C\/(1 - L)$ resulta $L_"stat" = theta eta \/ (theta eta + 1 - eta) = Theta(1)$ y $C_"stat" \/ K_"stat" = delta c_w (K_"stat" \/ L_"stat")^d = Theta(A^(-d\/r)) -> 0$ (y análogamente bajo trabajo fijo $overline(L)$). En consecuencia, la trayectoria estacionaria rinde utilidad $-eta(1 + d)\/(r(1 - beta)) log A + O(1)$, estrictamente dominada por _cake-eating_ puro $-eta\/(r(1 - beta)) log A + O(1)$ para todo $A$ grande.
     En ambos casos $K_"stat" (A) in.not G_A (K_"stat" (A))$, probando que todo óptimo en $(0, S_A^+]$ converge asintóticamente a $0$ o escapa de $(0, b_A]$.
  3. *(Regularidad local, envolvente de Milgrom--Segal y unicidad $S_A^- = S_A^+$):* Sea $V_"surv" (K)$ (resp. $V_"ext" (K)$) el supremo del problema restringido a trayectorias con $liminf_(t -> oo) K_t > 0$ (resp. $K_t -> 0$). En cualquier vecindad de un punto de indiferencia $K in [S_A^-, S_A^+] subset (kappa_A, b_A]$, todo sucesor extinto $s in G^-(K)$ y todo sucesor de supervivencia $s' in G^+(K)$ satisfacen $s' > K >= s$ (por monotonía y ausencia de óptimos estacionarios), con correspondencias compactas y funciones valor continuas. Los eslabones 1 y 2 verifican directamente las cuatro hipótesis del Lema 3 de MR, entregando la unicidad $S_A^- = S_A^+ = S_A$ de forma inmediata; de modo equivalente, aplicando el teorema de la envolvente direccional de Milgrom y Segal (2002) (análogo exacto del Lema 8 de MR), la derivada lateral izquierda de $V_"surv"$ y la derivada lateral derecha de $V_"ext"$ satisfacen la identidad exacta:
     $ V'_("surv") (K^-) = min_(s in G^+(K)) partial_K u_"red" (K, s) > max_(s in G^-(K)) partial_K u_"red" (K, s) = V'_("ext") (K^+), $
     donde la desigualdad estricta proviene de las diferencias crecientes estrictas $r_("red", K s) > 0$, impidiendo un segundo cruce descendente de $V_"surv" - V_"ext"$ y forzando $S_A^- = S_A^+ = S_A$ para todo $A$ suficientemente grande.
]

== Isomorfismo Finito, Demostración Analítica Pura de $S_A^"fix" (1) < S_A$ y Ley de Segundo Orden

El siguiente paso relaciona ambos problemas para productividad $A$ _finita_ arbitraria mediante un isomorfismo exacto de escalamiento y cierra analíticamente $S_A^"fix" (1) < S_A$ sin depender de verificación numérica.

#thm_box("Teorema", "3*", [Parte 2: Isomorfismo finito y prueba analítica pura de $S_A^"fix" (1) < S_A$])[
  1. *(Isomorfismo de oferta fija arbitraria):* Para todo $A > 0$ y todo nivel constante de trabajo $overline(L) in (0, 1]$, la homogeneidad grado $theta = 1 + r$ de $F_A (K, L)$ junto con el reescalamiento $tilde(K)_t = K_t \/ overline(L)$ inducen el isomorfismo exacto con la economía de capacidad plena ($overline(L) = 1$) a productividad $A overline(L)^r$:
     $ S_A^"fix" (overline(L)) = overline(L) thin S_(A overline(L)^r)^"fix" (1), #h(12pt) kappa_A^"fix" (overline(L)) = overline(L) thin kappa_(A overline(L)^r) >= kappa_A^"fix" (1) = kappa_A. $
  2. *(Criterio variacional y desigualdad estricta analítica $S_A^"fix" (1) < S_A$):* Evaluando ambos problemas en el punto de Skiba endógeno $S_A$, sea la prima de bienestar de capacidad plena frente al óptimo endógeno:
     $ Delta W_A^+ := V_A^"fix" (S_A; 1) - V_A^"endo" (S_A) >= Delta W_A^(pi^+) := J_A^"fix" (S_A; pi^+ |_(L=1)) - V_A^"endo" (S_A) > 0, $
     donde $pi^+ = (K_t^+, L_t^+)$ denota un óptimo productivo que escapa desde $K_0^+ = S_A$, y sea $Delta W_A^- := sup_(pi^- in cal(O)_-^"fix") [J_A^"fix" (pi^-) - V_A^"endo" (S_A)] = O(A^(-d\/(r(1+d))))$ la cota en trayectorias confinadas en $(0, S_A]$. Fijado cualquier $tilde(theta) in (beta^(-1), theta)$ como en la Parte 1, con $tilde(kappa) := (|log beta|) / (log tilde(theta)) in (kappa, 1)$ y $M = 2(1 + tilde(kappa))(1 + d)\/d$, para todo $A$ suficientemente grande el tiempo hasta alcanzar $k_t^+ >= (log A)^M$ a lo largo de $pi^+$ satisface la cota log-logarítmica pura:
     $ T_M (A) <= (1 + tilde(kappa)) / (|log beta|) log log A + O(1), #h(12pt) tilde(kappa) = (|log beta|) / (log tilde(theta)) in (kappa, 1). $
     En el instante $t^* = T_M (A)$, la ganancia intramarginal en $L = 1$ satisface $Delta W_A^(pi^+) >= beta^(T_M) g_(T_M) >= c_(10) A^(-d\/(r(1+d))) (log A)^(1 + tilde(kappa)) >> O(A^(-d\/(r(1+d)))) = Delta W_A^-$. En consecuencia, existe un umbral explícito $A_0$ tal que para *todo* $A >= A_0$ se cumple estrictamente *$S_A^"fix" (1) < S_A$* por demostración analítica pura.
]

#proof_block(title: "Demostración del Teorema 3*, Parte 2")[
  La homogeneidad de grado $theta = 1 + r$ rinde $F_A (overline(L) tilde(K), overline(L)) = overline(L) F_(A overline(L)^r) (tilde(K), 1)$ y $eta log(overline(L) tilde(C)_t) = eta log tilde(C)_t + eta log overline(L)$, estableciendo el isomorfismo finito. En $K_0 = S_A$, existen tanto un óptimo productivo $pi^+$ como un óptimo extinto alcanzando $V_A^"endo" (S_A)$. Para las trayectorias confinadas $pi^- in cal(O)_-^"fix"$ bajo $K_t^"f" <= S_A <= c_+ A^(-1\/r)$, comparando $V_A^"fix" (K_t^"f"; 1)$ con el piso _cake-eating_ se deduce el piso asintótico $C_t^"f" \/ K_t^"f" >= chi_p^"fix" = Omega(1) > 0$; equipando $(K_t^"f")$ con trabajo $tilde(L)_t = c_0 A^(-d\/(r(1+d)))$ la pérdida CES y el costo de ocio rinden $(F_A (K_t^"f", 1) - F_A (K_t^"f", tilde(L)_t)) \/ C_t^"f" = O(A^(-d\/(r(1+d))))$ y $Delta W_A^- = O(A^(-d\/(r(1+d))))$. Restando al valor normalizado $v_A (k) := V_A (A^(-1\/r) k) + eta\/(r(1-beta)) log A$, basta probar $Delta W_A^(pi^+) >> A^(-d\/(r(1+d)))$ en cuatro eslabones analíticos puros (fijado $tilde(theta) in (beta^(-1), theta)$ y $tilde(kappa) := |log beta| \/ log tilde(theta) in (kappa, 1)$):
  1. *(Invariancia de $[0, k_*]$ y salida $T_epsilon.alt (A) <= |log beta|^(-1) log log A + O(1)$):* Puesto que $k_0^+ = A^(1\/r) S_A > (delta\/c_K)^(1\/r) =: k_*$ para $A$ grande y cualquier trayectoria en $[0, k_*]$ con $k_(t+1) <= k_*$ es no creciente en $K_t$ (lo que acota su valor normalizado por $v^"cake" (k_*) + O(1)$), el óptimo productivo $pi^+$ satisface $k_t^+ > k_*$ para todo $t >= 0$. Fijemos $epsilon.alt > 0$ suficientemente pequeño tal que en $k in (k_*, k_* + epsilon.alt]$ el consumo máximo compatible con permanecer en $(k_*, k_* + epsilon.alt]$ cumpla $eta log macron(c)(epsilon.alt) <= (1 - beta) v^"cake" (k_*) - 1$. Si $pi^+$ demora $T_epsilon.alt (A) := inf{t >= 0 : k_t^+ > k_* + epsilon.alt}$ pasos dentro de $(k_*, k_* + epsilon.alt]$, iterar Bellman hasta $T_epsilon.alt$ da $v^"cake" (k_*) <= v_A^"endo" (k_0^+) <= (1 - beta^(T_epsilon.alt))(v^"cake" (k_*) - 1\/(1-beta)) + beta^(T_epsilon.alt) v_A^"endo" (k_(T_epsilon.alt)^+)$. Como $v_A^"endo" (k_(T_epsilon.alt)^+) <= C_0 log A + O(1)$, se obtiene $beta^(T_epsilon.alt (A)) [C_0 log A + O(1)] >= 1$, implicando $T_epsilon.alt (A) <= |log beta|^(-1) log log A + O(1)$.
  2. *(Piso de bienestar en $k_* + epsilon.alt$ vía crecimiento doblemente exponencial):* Desde cualquier estado $k >= k_* + epsilon.alt$, la política de Fases I--III de la Parte 1 alcanza escala macroscópica en $T_1 (epsilon.alt) + |log tilde(theta)|^(-1) log log A$ pasos (con $beta tilde(theta) > 1$), entregando el piso $v_A^"endo" (k_* + epsilon.alt) >= c_1 (log A)^(1 - tilde(kappa)) - C_2$, donde $tilde(kappa) = |log beta| \/ log tilde(theta) in (kappa, 1)$.
  3. *(Acotación de $T_M (A)$ entre $k_* + epsilon.alt$ y $(log A)^M$):* Sea $T_M (A) := inf{t >= 0 : k_t^+ >= (log A)^M}$ con $M = 2(1 + tilde(kappa))(1 + d)\/d$. Mientras $k_t^+ < (log A)^M$, la utilidad normalizada instantánea verifica $u_"norm" (k_t^+, L_t^+) <= eta log(q k_t^+ + c_K (k_t^+)^theta) <= eta theta M log log A + C_3$, mientras que $v_A^"endo" (k_(T_M)^+) <= C_4 log A$. Iterando Bellman entre $T_epsilon.alt$ y $T_M$: $c_1 (log A)^(1 - tilde(kappa)) - C_2 <= eta theta M (log log A)\/(1 - beta) + beta^(T_M - T_epsilon.alt) C_4 log A$, lo cual fuerza $beta^(T_M - T_epsilon.alt) >= c'_6 (log A)^(-tilde(kappa))$ y, combinando con el Eslabón 1, *$T_M (A) <= (1 + tilde(kappa)) / (|log beta|) log log A + O(1)$* y $beta^(T_M (A)) >= c_6 (log A)^(-1 - tilde(kappa))$.
  4. *(Ganancia instantánea en $t^* = T_M (A)$):* En el primer instante de alcance $t^* = T_M (A)$ se cumple $k_(t^*)^+ >= (log A)^M$, de modo que $K_(t^*)^+ >= A^(-1\/r) (log A)^M$; además, como $k_(t^* - 1)^+ < (log A)^M$, vale también $K_(t^*)^+ <= q K_(t^* - 1)^+ + F_A (K_(t^* - 1)^+, 1) <= A^(-1\/r) [q (log A)^M + c_K (log A)^(M theta)] -> 0$, lo que justifica $F_1 (K_(t^*)^+, 1) asymp (K_(t^*)^+)^theta$ y $q K_(t^*)^+ \/ (A (K_(t^*)^+)^theta) = (k_(t^*)^+)^(-r) <= (log A)^(-M r) -> 0$, acotando el consumo por $C_(t^*)^+ <= C_5 A F_1 (K_(t^*)^+, 1)$. Sea $L_"cut" := min{1\/2, (K_(t^*)^+)^(d\/(1+d))}$. Si $L_(t^*)^+ >= L_"cut"$, suprimir el ocio aporta $(1 - eta)|log(1 - L_(t^*)^+)| >= (1 - eta) L_"cut" >= c_7 min{1, A^(-d\/(r(1+d))) (log A)^(M d\/(1+d))}$. Si $L_(t^*)^+ < L_"cut"$, entonces $K_(t^*)^+ \/ L_(t^*)^+ > (K_(t^*)^+)^(1\/(1+d))$ y, por monotonía CES, la brecha productiva cumple $(F_A (K, 1) - F_A (K, L_(t^*)^+)) \/ C_(t^*)^+ >= c_8 min{1, (K_(t^*)^+ \/ L_(t^*)^+)^d} \/ C_5 >= c_9 min{1, (K_(t^*)^+)^(d\/(1+d))}$. Ambos casos garantizan $g_(t^*) >= c'_9 min{1, A^(-d\/(r(1+d))) (log A)^(M d\/(1+d))}$. Sustituyendo $M = 2(1+tilde(kappa))(1+d)\/d$ ($M d \/ (1 + d) = 2(1 + tilde(kappa))$), resulta:
     $ Delta W_A^+ >= Delta W_A^(pi^+) >= beta^(T_M (A)) g_(T_M (A)) >= c_(10) A^(-d\/(r(1+d))) (log A)^(1 + tilde(kappa)) >> O(A^(-d\/(r(1+d)))) = Delta W_A^-, $
     cerrando analíticamente $S_A^"fix" (1) < S_A$ para todo $A$ suficientemente grande.
]

#thm_box("Observación", "1", [Ley asintótica heurística de segundo orden y sensibilidad envolvente (validada hasta $A = 10^8$)])[
  Sea $k_* := (delta\/c_K)^(1\/r)$, $lambda_K := q + theta delta > 1$ el valor propio de expansión linealizada del mapa óptimo alrededor de $k_*$, $mu_K := |log beta| \/ log lambda_K$ y $kappa = |log beta| \/ log theta$. Al equilibrar heurísticamente la pérdida logarítmica inicial de permanencia cerca de $k_*$ frente a la recompensa productiva futura mediante el balance trascendental (omitiendo eventuales correcciones logarítmicas de la fracción óptima de consumo $phi(Delta_k) -> 0$ cerca de $k_*$):
  $ (eta) / (1 - beta) log(k_* / Delta_k) + C_0 approx Delta_k^(mu_K) [C_oo (log A)^(1 - kappa) + C_"const"], $
  donde $C_"const" approx |v^"cake" (k_*)|$ recoge la constante de nivel de _cake-eating_, emerge la ley asintótica heurística validada cuantitativamente en la Tabla 3 hasta $A = 10^8$:
  1. *(Convergencia ultraslow de segundo orden):* El desvío $Delta_k (A) := A^(1\/r) S_A - k_*$ escala como $Delta_k (A) asymp ([log log A] \/ [(log A)^(1 - kappa)])^(1\/mu_K)$; en nuestra calibración ($lambda_K = 1.04$, $mu_K = 0.77661$, $kappa = 0.07512$, $(1 - kappa)\/mu_K = 1.19092$, $1\/mu_K = 1.28765$), el gran desplazamiento constante $C_"const" approx 336$ actúa como freno pre-asintótico junto al exponente moderado $1 - kappa = 0.9249$, explicando cuantitativamente por qué en $A = 10^8$ persiste aún un $+3.9\%$ ($A^2 S_A = 0.000831$ frente a $0.000800$).
  2. *(Brecha relativa por envolvente de Milgrom--Segal):* Aplicando el argumento envolvente al cruce único en $S_A$, la ventaja relativa entre umbrales obedece $(S_A - S_A^"fix" (1)) \/ S_A asymp Delta_k (A) dot Delta W_A^+ asymp (log log A)^(1 + 1\/mu_K) \/ (log A)^(1 + (1 - kappa)\/mu_K)$ (confirmándose en la Tabla 3 la estabilidad suave de la razón envolvente $(S_A - S_A^"fix" (1)) \/ (S_A dot Delta_k dot Delta W_A^+)$ entre $29.35$ en $A = 10^2$, $27.84$ en $10^3$, $23.95$ en $10^6$ y $22.36$ en $10^8$).
]

La Tabla 3 reporta la verificación VFI continua en malla logarítmica refinada en $k = A^2 K$ desde $A = 0.75$ hasta $A = 10^8$ (alcanzando capitales estacionarios del orden de $k_"ss" tilde.op A^(5\/2) = 10^(20)$ sin truncamiento de grilla ni evaluación desalineada de puntos). La auditoría numérica sobre esta malla logarítmica confirma cinco leyes exactas en *todas* las filas:
1. *Desigualdad variacional respetada globalmente:* se cumple $0 < Delta W_A^(pi^+) <= Delta W_A^+$ en absolutamente toda la tabla (por ejemplo, $8.357 <= 8.749$ en $A = 0.75$, $0.782 <= 0.794$ en $A = 100$, y $0.513 <= 0.513$ en $A = 10^8$).
2. *Decaimiento polilogarítmico y tasa de segundo orden:* El diferencial completo cumple $Delta W_A^+ = Theta(beta^(T_"esc" (A))) = Theta((log log A)\/(log A))$ (donde $(log A)^(-kappa)$ representa únicamente el factor de la Fase II antes de incorporar el cuello de botella inicial $T_1 (Delta_k)$), con $T_"esc" (A)$ creciendo de $97$ ($A = 0.75$) a $126$ ($A = 10^8$, $T_"esc" \/ log log A$ convergiendo de $75.96$ en $10^2$ a $43.25$ en $10^8$), mientras $Delta_k$ pasa de $0.000052$ ($10^2$) a $0.000031$ ($10^8$) en línea con la Observación 1.
3. *Límite estacionario exacto del trabajo:* en la cola superior, $L_"endo"$ *no* converge a $1$, sino exactamente al punto fijo estacionario interior:
   $ L_"ss" = (theta eta) / (theta eta + (1 - eta)) = (1.5 times 0.70) / (1.5 times 0.70 + 0.30) = 7 / 9 approx 0.777778 < 1, $
   confirmado por VFI hasta cinco cifras decimales ($0.7778$ en $A = 10^6$ y $10^8$).
4. *Exponente armónico $O(A^(-1))$ en la cuenca baja:* con $d = 1, r = 1\/2$, el diferencial en la trampa decrece a tasa $Delta W_A^- = O(A^(-d\/(r(1+d)))) = O(A^(-1))$. En $A = 10^8$, $beta^(T_"esc") = beta^126 = 0.02154$, dominando al término $A^(-1) = 10^(-8)$ por más de seis órdenes de magnitud ($beta^(T_"esc") dot A = 2.15 times 10^6$).
5. *Confirmación cuantitativa del teorema puro:* la VFI confirma $A^2 S_A^"fix" (1) < A^2 S_A$ en todas las filas (razón descendiendo de $1.01981$ en $A = 0.75$ a $1.00035$ en $A = 10^8$), en perfecta concordancia cuantitativa con la demostración analítica pura del Teorema 3\* Parte 2 y la ley envolvente de segundo orden ($"rel_gap" \/ (Delta_k Delta W_A^+) = 29.35 -> 22.36$).

#v(0.3em)
#figure(
  table(
    columns: (0.9fr, 1.0fr, 1.0fr, 0.9fr, 0.85fr, 0.85fr, 0.75fr, 0.85fr),
    inset: 5.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.4pt)[$A$],
      text(fill: white, weight: "bold", size: 8.4pt)[$A^2 S_A^"fix" (1)$],
      text(fill: white, weight: "bold", size: 8.4pt)[$A^2 S_A$],
      text(fill: white, weight: "bold", size: 8.4pt)[Razón],
      text(fill: white, weight: "bold", size: 8.4pt)[$Delta W_A^(pi^+)$],
      text(fill: white, weight: "bold", size: 8.4pt)[$Delta W_A^+$],
      text(fill: white, weight: "bold", size: 8.4pt)[$T_"esc"$],
      text(fill: white, weight: "bold", size: 8.4pt)[$L_"ss"$],
    ),
    [$0.75$], [$0.000875$], [$0.000892$], [$1.01981$], [$8.357$], [$8.749$], [$97$], [$0.7817$],
    [$1.50$], [$0.000867$], [$0.000877$], [$1.01079$], [$5.095$], [$5.292$], [$106$], [$0.7803$],
    [$3.00$], [$0.000863$], [$0.000869$], [$1.00614$], [$3.133$], [$3.231$], [$110$], [$0.7795$],
    [$10.0$], [$0.000858$], [$0.000861$], [$1.00275$], [$1.530$], [$1.566$], [$113$], [$0.7786$],
    [$30.0$], [$0.000855$], [$0.000856$], [$1.00169$], [$0.999$], [$1.017$], [$114$], [$0.7783$],
    [$100$], [$0.000851$], [$0.000852$], [$1.00122$], [$0.782$], [$0.794$], [$116$], [$0.7780$],
    [$10^3$], [$0.000846$], [$0.000846$], [$1.00087$], [$0.664$], [$0.668$], [$118$], [$0.7779$],
    [$10^6$], [$0.000835$], [$0.000836$], [$1.00048$], [$0.562$], [$0.562$], [$123$], [$0.7778$],
    [$10^8$], [$0.000831$], [$0.000831$], [$1.00035$], [$0.513$], [$0.513$], [$126$], [$0.7778$],
  ),
  caption: [Tabla 3: Verificación VFI en escala $log k$ hasta $A = 10^8$ (Teorema 3\* y Observación 1). Nótese $0 < Delta W_A^(pi^+) <= Delta W_A^+ -> 0^+$, razón envolvente $29.35 -> 22.36$, y $L_"ss" -> 7\/9$.],
)

#figure(
  image("fig2_scaling_es.svg", width: 100%),
  caption: [Figura 2: (a) Convergencia uniforme de $A^2 S_A^"fix" (1)$ y $A^2 S_A$ hacia $(delta\/c_K)^2 = 0.000800$ (e inserto $beta = 0.90$ del Corolario 2\*). (b) Prueba analítica pura $beta^(T_M) g_(T_M) >> O(A^(-1))$, decaimiento de $Delta W_A^(pi^+) <= Delta W_A^+$ y ley de segundo orden.],
)

// ============================================================================
// SECCIÓN 5: CEGIS-PWL Y BARRERAS ESTOCÁSTICAS DE DOOB
// ============================================================================
= Síntesis Adaptativa CEGIS-PWL y Supervivencia Estocástica de Doob

En las secciones precedentes los afilamientos deterministas dependían de barreras afines calculadas a mano o testigos de $25$ pasos sobre mallas discretas. Para abordar problemas acoplados, continuos en bandas paramétricas de descuento $tilde(beta)$ y con horizontes aleatorios de crisis, introducimos un motor general de *_síntesis adaptativa mediante programación lineal y contraejemplos guiados (_CEGIS-PWL_)_*.

== Arquitectura Proposer--Verifier y Representación Log-PWL Exacta

El principio de diseño separa estrictamente la búsqueda (_Proposer_) de la certificación matemática (_Verifier_):
1. *Representación exacta log-PWL (100% LP determinista):* Toda función barrera $Psi(K)$, $B_theta (K)$ o testigo $W(K)$ se parametriza como una función continua lineal por tramos en log-capital $z = log K$ sobre nodos estrictamente crecientes $k_0 < k_1 < dots < k_n$, prolongada analíticamente con pendientes asintóticas exactas $s_"lo" = eta_- \/ (1 - beta_-)$ en $(0, k_0]$ y $D_"hi" = eta_+ \/ (1 - beta_+)$ en $[k_n, oo)$. Los seis Casos 1--6 se sintetizan determinísticamente mediante programación lineal dispersa en HiGHS optimizando directamente las alturas nodales, garantizando reproducibilidad bit-exacta sin optimización estocástica ni dependencias de aprendizaje profundo.
2. *Bucle CEGIS-LP con inserción adaptativa de contraejemplos:* En cada ronda, el _Proposer_ resuelve un programa lineal con restricciones dispersas (matrices CSR/CSC de $2$ elementos no nulos por fila) que impone las desigualdades de Bellman sobre una grilla activa de $(K, L, s)$ junto con monotonicidad en $M$ y cotas de derivada $< b$ y $< h$, regularizando la variación total de log-pendientes. A continuación, el _Verifier_ audita la barrera continua resultante en todo el dominio $(0, oo) times [0, 1) times [0, 1) times cal(P)$ mediante Branch-and-Bound (B&B) 3D y 1D usando forma centrada y monotonía, devolviendo los peores contraejemplos continuos para enriquecer los nodos y las filas del LP en la ronda siguiente.
3. *Auditoría terminal por intervalos con redondeo dirigido:* El $100\%$ de las pruebas publicadas aquí depende *únicamente* del _Verifier_. Toda hoja terminal del árbol B&B —así como las colas analíticas $(0, k_0]$ y $[k_n, oo)$ y las salidas adversas— es re-auditada exhaustivamente en aritmética de intervalos de redondeo dirigido (kernel nativo compilado en Rust vía `f64::next_down`/`next_up` para las millones de cajas 3D e intervalos `Decimal` de $50$ dígitos en Python para colas analíticas y auditorías 1D, con respaldo $100\%$ equivalente en Python/Numba).

== Caso 1: Síntesis LP Determinista, Cadena No Estacionaria ($5 -> 4$) y Cascada Hasta $b_"ext" = 0.0030$

#thm_box("Proposición", "2", [Certificado determinista CEGIS-LP (Caso 1A) y descomposición no estacionaria (Caso 1C)])[
  Sea $(B_theta, Psi, W)$ la tripleta continua log-PWL sintetizada determinísticamente mediante HiGHS-LP sobre la caja completa $cal(P)$ ($B_theta$ de $57$ nodos —con versión podada/compacta de $22$ nodos— sobre $M = [0.10, 0.28)$; $Psi$ de $193$ nodos con colas analíticas en $10^(-4)$ y $90$; $W$ de $74$ nodos sobre $[0.10, 5.5]$). Bajo auditoría B&B 3D/1D sin `libm` ($d_"ub,iv"^(B_theta) = -0.000200 <= 0$, $d_"ub,iv"^Psi = -0.000100 <= 0$, $d_"ub,iv"^W = -4.51 times 10^(-7) <= 0$, e $inf_(M_0) Psi' = 91.23 > 6.4234$):
  1. En los extremos de $M$, $B_theta (0.10) = -56.6905$ y $B_theta (0.28) = -52.3524$; frente al testigo de MR-Tabla 4 y techo $Psi^sharp$, el margen en $M$ alcanza $19.0600$ (frente a techo $24.5153$) y el plazo cae a *$T_theta = 9$*. Acoplando $(Psi, W, B_theta)$, el margen sube a $21.0857$ (techo $24.2013$) y comprime el plazo certificado a *$T_"full" = 5$*.
  2. *Descomposición de la brecha ($5 -> 4 = tau_H^"VFI"$):* Sintetizando cadenas no estacionarias de horizonte finito $\{J_k\}_(k=0)^T$ ($J_0 >= Psi$, $J_k >= cal(T)_(cal(P))^+ J_(k-1)$ auditadas por B&B 3D, $W > J_T$ en $M$), obtenemos *$T_"ns" (cal(P)) = 5$* sobre la caja completa $cal(P)$ (holgura $+0.3055$) y *$T_"ns" (theta_0) = 4 = tau_H^"VFI"$* en el punto central $theta_0 = (0.75, 0.92, 0.97, 0.70)$ (holgura $+0.0942$). Así, el único período adicional ($5$ vs. $4$) proviene íntegramente de la incertidumbre paramétrica de la caja $cal(P)$, saturándose la cota en el punto central sin brecha estructural.
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
      text(fill: white, weight: "bold", size: 8.3pt)[Configuración LP (sin PyTorch)],
      text(fill: white, weight: "bold", size: 8.3pt)[Nodos $B_theta$],
      text(fill: white, weight: "bold", size: 8.3pt)[$T_theta$ (MR)],
      text(fill: white, weight: "bold", size: 8.3pt)[$T_"full"$],
      text(fill: white, weight: "bold", size: 8.3pt)[$d_"ub,iv"^(B_theta)$],
      text(fill: white, weight: "bold", size: 8.3pt)[Síntesis (s)],
    ),
    [CEGIS-LP base (sin poda)], [$57$], [$9$], [$5$], [$-0.000200$], [$2.29$],
    [CEGIS-LP compacto (grilla podada)], [$22$], [$9$], [$5$], [$-0.000200$], [$0.95$],
  ),
  caption: [Tabla 4: Ablación de compacidad de la síntesis LP determinista en Caso 1A (HiGHS ralo reproducible sobre la caja completa $cal(P)$).],
)

En la Figura 6 (pág. 21) de MR (2026), los autores señalan como principal limitación cuantitativa la ausencia de plazo explícito entre el umbral de Skiba $S_A < 0.0025$ y $K_0 = 0.10$ («_no explicit deadline_»); nuestra Proposición 1\* redujo ese borde de $0.10$ a $0.05$. La siguiente proposición cierra casi íntegramente esa brecha:

#thm_box("Proposición", "2*", [Cascada continua CEGIS-LP casi hasta el umbral de Skiba ($b_"ext" = 0.0030$, Caso 1B)])[
  Consideremos el dominio ampliado $[b_"ext", 0.28)$ con $b_"ext" = 0.0030$ (cerrando el *$99.5\%$* de la brecha $[0.0025, 0.10)$ reportada en la Figura 6 de MR y el *$98.6\%$* del ancho $(S_A, 0.10)$ entre $S_A = 0.001588$ y $0.10$), particionado en $16$ subcajas ortogonales $(4_A times 4_beta)$ de $(A, beta)$ con consumo de salida en $[0.0030, 0.28)$ evaluado globalmente mediante $l_0 = 0.1695 > h\/2 = 0.14$ (cumpliendo la condición de dominancia global de la tangente de la Proposición 1\*\* y del Apéndice F.3 de MR sobre todo el rango $[0.0030, 0.28)$). En cada una de las $16$ subcajas se certifican continuamente $(Psi, W)$, derivada $< b_"ext"$, salida adversa positiva por debajo de $b_"ext"$ (mínimo global $+0.1326$) y una cascada contigua de $5$ barreras de permanencia sobre las subregiones:
  $ [0.003, 0.006]_(T_1 <= 21), thin [0.006, 0.015]_(T_2 <= 13), thin [0.015, 0.040]_(T_3 <= 8), thin [0.040, 0.100]_(T_4 <= 5), thin [0.100, 0.280]_(T_5 <= 5). $
  Como la ausencia de salida inferior por debajo de $b_"ext" = 0.0030$ implica $S_A < 0.0030$ en toda la caja $cal(P)$, el Teorema 8 y la ecuación (F.1) de MR garantizan monotonicidad estricta $K_(t+1) > K_t$ a lo largo de toda trayectoria óptima de escape en $(S_A, 0.60]$, lo cual impide que una senda óptima retroceda a una etapa anterior ya superada. En consecuencia, para toda condición inicial $K_0 in [0.0030, 0.28)$ y todo parámetro en $cal(P)$, el tiempo total máximo de escape hasta $H = [0.28, oo)$ queda certificado en a lo sumo *$T_"total" <= 21 + 13 + 8 + 5 + 5 = 52$* períodos.
]

== Parada Opcional de Doob y Dicotomía VFI Estocástica (Tabla 5)

Para certificar probabilidades de supervivencia cuando la economía enfrenta choques agregados de ruina o regímenes persistentes de recesión, utilizamos el siguiente argumento probabilístico.

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

#thm_box("Corolario", "3", [Reducción a ruina, probabilidad de supervivencia y tiempo medio de salida])[
  Bajo los supuestos del Lema 2:
  1. *(Reducción con valor absorbente de ruina $U_0$):* Si en cada período ocurre transición irreversible hacia un estado absorbente de valor $U_0$ con probabilidad $p in [0, 1)$, la normalización $tilde(V) = V - U_0$, $tilde(B) = B - U_0$, $tilde(u) = u - (1 - beta) U_0$ cancela idénticamente el término de salto $beta p U_0$ mediante el desplazamiento $-(beta p U_0)\/(1 - tilde(beta)_p)$, reduciendo el problema con $V_"ruin" = 0$ a la ecuación de Bellman con descuento efectivo $tilde(beta)_p = beta (1 - p)$ y recompensas inalteradas salvo la constante aditiva de normalización. Si una política satisface $J_(x_0) (pi; tilde(beta)_p) > B(x_0) + tilde(beta)_p^T sup_(x in M) [Psi(x) - B(x)]$ en ausencia de quiebra durante $T = T^*(p)$ períodos, entonces todo óptimo sobrevive la transición antes de $T^*(p)$ con probabilidad al menos $Pr(tau_H < oo | K_0 = b, G) >= (1 - p)^(T^*(p))$.
  2. *(Brecha de Doob $epsilon.alt_0$ y finitud de $E[tau]$ en Markov):* Sea $y_"max" = q_+ h + F_(A_+) (h, 1)$ la cota máxima de capital en un salto ascendente desde $M$, y defínanse $m_inf := min_(omega in {G, B}) inf_(K in M) [W_omega (K) - B_omega (K)]$, $d_"stay" := max_(omega') sup_(K in M) [Psi_(omega') (K) - B_(omega') (K)]$ y $d_"exit" := max_(omega') sup_(y in [h, y_"max"]) [Psi_(omega') (y) - B_(omega') (y)]$ (bajo extensión constante $B_(omega') (y) = B_(omega') (h)$ en $[h, y_"max"]$ con $Psi_(omega')$ creciente, $d_"exit" = max_(omega') [Psi_(omega') (y_"max") - B_(omega') (h)]$, y cuando $B_omega$ es afín o no decreciente los extremos coinciden con los valores en $b$ y en $B_(*, omega')$). Si existe $T_0 >= 1$ tal que
     $ epsilon.alt_0 := (m_inf - beta_+^(T_0) d_"stay") / (beta_0^1 d_"exit" - beta_+^(T_0) d_"stay") > 0 #h(10pt) ("con " beta_0^1 = 1 "o" beta_0^1 = beta_+ "si " tau >= 1), $
     entonces cualquier óptimo con ausencia de salida inferior c.s. verifica $Pr(tau <= T_0 | K_0 in M, omega_0) >= epsilon.alt_0$ uniformemente sobre $M times {G, B}$, por lo que $Pr(tau > k T_0) <= (1 - epsilon.alt_0)^k -> 0$, $Pr(tau = oo) = 0$ y $E[tau] <= T_0 \/ epsilon.alt_0 < oo$.
]

#proof_block(title: "Demostración del Corolario 3")[
  Para la parte (1), en ausencia de quiebra durante $0 <= t < T^*(p)$ (evento de probabilidad $(1 - p)^(T^*(p))$), toda historia que permanece en $M$ hasta $T^*(p)$ recibe a lo sumo $B(x_0) + tilde(beta)_p^(T^*(p)) sup_M (Psi - B) < W(x_0)$ tras cancelar la constante de ruina $(beta p U_0)\/(1 - tilde(beta)_p)$; como los testigos $W$ alcanzan al menos $W(x_0)$ condicionando a la trayectoria de permanencia sin ruina previa, toda senda óptima desde $K_0 in M$ debe haber cruzado $h$ o haberse topado con ruina antes de $T^*(p)$, implicando $Pr(tau_H < oo | K_0 = b, G) >= (1 - p)^(T^*(p))$. Para la parte (2), partiendo de cualquier $(K_0, omega_0) in M times {G, B}$, el Lema 2 en $T = T_0$ acota $W_(omega_0) (K_0) <= E[J(pi)] <= B_(omega_0) (K_0) + Pr(tau <= T_0) beta_0^1 d_"exit" + (1 - Pr(tau <= T_0)) beta_+^(T_0) d_"stay"$ (donde $tau >= 1$ en $K_0 in M$ y $K_tau in [h, y_"max"]$ cuando $tau <= T_0$, y $K_(T_0) in M$ cuando $tau > T_0$). Reordenando y acotando $W_(omega_0) (K_0) - B_(omega_0) (K_0) >= m_inf$ uniformemente en $M times {G, B}$ rinde exactamente $Pr(tau <= T_0 | K_0 in M, omega_0) >= epsilon.alt_0 > 0$. Aplicando iterativamente la propiedad fuerte de Markov en múltiplos $k T_0$ ($k >= 1$), la probabilidad de permanecer sin salir en $k$ bloques consecutivos cumple $Pr(tau > k T_0) <= (1 - epsilon.alt_0)^k -> 0$, garantizando $Pr(tau = oo) = 0$ y $E[tau] <= T_0 sum_(k=0)^oo (1 - epsilon.alt_0)^k = T_0 \/ epsilon.alt_0 < oo$.
]

Así como el Teorema 7 de MR establece una equivalencia converso-determinista bajo compacidad (selección óptima de $H$ si y solo si existe una FPBB estricta), el siguiente teorema eleva el Lema 2 a teoría general de control óptimo estocástico:

#thm_box("Teorema", "7*", [Completitud estocástica: converso para FPBB estocásticas de Doob])[
  Considérese un proceso de decisión Markoviano compacto sobre $cal(X) = [b, K_"max"] times Omega$ ($Omega$ finito, $beta in (0, 1)$, $y_"max" <= K_"max"$), con ausencia de salida inferior c.s. ($K_(t+1) >= b$) desde $cal(X)_M = [b, h) times Omega$, retorno $u$ continuo, monótono creciente en consumo y uniformemente acotado en el compacto factible, correspondencia factible continua y compacta, y funciones valor continua del problema libre $V$ y del problema restringido al cierre $[b, h]$:
  $ V_M^"stay" (K, omega) := sup{E_(K, omega) [sum_(t=0)^oo beta^t u(c_t, L_t)] : K_t in [b, h] thin forall t >= 0}, $
  satisfaciendo $V(h, omega) > V_M^"stay" (h, omega)$ para todo $omega in Omega$. Son equivalentes:
  1. *(Escape uniforme de Doob):* Existe $C < oo$ tal que todo óptimo markoviano estacionario $pi^*$ satisface $sup_(x in cal(X)_M) E_x^(pi^*) [tau_H] <= C$ (equiv., existen $T_0 >= 1$ y $epsilon.alt_0 > 0$ con $inf_(x in cal(X)_M) Pr_x^(pi^*) (tau_H <= T_0) >= epsilon.alt_0$, implicando escape casi seguro $Pr_x^(pi^*) (tau_H < oo) = 1$).
  2. *(Brecha estricta de valor):* $delta_0 := inf_(x in cal(X)_M) [V(x) - V_M^"stay" (x)] > 0$.
  3. *(Existencia de FPBB estocástica estricta de Doob):* Existe una tripleta acotada $(Psi, W, B)$ (e incluso una tripleta continua log-PWL con un número finito de nodos) que satisface las desigualdades de súper-barrera, testigo y permanencia extendida del Lema 2 junto con $inf_(cal(X)_M) (W - B) > 0$ y brecha uniforme de Doob $epsilon.alt_0 > 0$ en el Corolario 3.
]

#proof_block(title: "Demostración del Teorema 7*")[
  *(3) $=>$ (1):* Sigue inmediatamente del Corolario 3 (parte 2), obteniendo $inf_(cal(X)_M) Pr_x (tau_H <= T_0) >= epsilon.alt_0 > 0$ y $sup_(cal(X)_M) E_x [tau_H] <= T_0 \/ epsilon.alt_0 < oo$. Inversamente, bajo (1), fijando $T_0 := ceil(2 C)$ la desigualdad de Markov rinde $Pr_x^(pi^*) (tau_H > T_0) <= C \/ T_0 <= 1\/2$, dando $inf_(cal(X)_M) Pr_x^(pi^*) (tau_H <= T_0) >= 1\/2 > 0$. \
  *(1) $=>$ (2):* Supóngase por contradicción que $delta_0 = inf_(cal(X)_M) (V - V_M^"stay") = 0$. Como $V$ y $V_M^"stay"$ son continuas sobre el compacto $[b, h] times Omega$, el conjunto cerrado $E_0 := {x in [b, h] times Omega : V(x) = V_M^"stay" (x)}$ es no vacío y, dado $V(h, omega) > V_M^"stay" (h, omega)$ por hipótesis, satisface $E_0 subset cal(X)_M$. Por optimalidad de Bellman del problema restringido $V_M^"stay"$ en el compacto $[b, h] times Omega$, existe una política estacionaria markoviana factible $tilde(pi)$ que mantiene $K_t in [b, h]$ para todo $t >= 0$ y alcanza $V_M^"stay" (x) = V(x)$ sobre todo $x in E_0$, dejando por consiguiente al cerrado $E_0$ invariante (pues cualquier transición óptima desde $x in E_0$ hacia $y$ con $V(y) > V_M^"stay" (y)$ haría imposible la igualdad $V(x) = V_M^"stay" (x)$). Pegando $tilde(pi)$ sobre el cerrado invariante $E_0$ con una política estacionaria markoviana libre óptima fuera de $E_0$ se construye una política estacionaria markoviana óptima global $pi^*$ que en cualquier $x_0 in E_0 subset cal(X)_M$ verifica $Pr_(x_0)^(pi^*) (tau_H = oo) = 1$, contradiciendo (1). \
  *(2) $=>$ (3):* Extendiéndose $V_M^"stay"$ sobre $[b, y_"max"] times Omega$ mediante la truncación $B(K, omega) := V_M^"stay" (min{K, h}, omega)$, verificamos la desigualdad extendida del Lema 2: si la acción cae en $K' in [b, h)$, vale $u + beta E[B(K', omega')] = u + beta E[V_M^"stay" (K', omega')] <= V_M^"stay" (K, omega) = B(K, omega)$; si sale hacia $K' in [h, y_"max"]$, al reemplazar $K'$ por $h$ el consumo $c = q K + F_A (K, L) - K'$ sube estrictamente mientras $B(K', omega') = V_M^"stay" (h, omega')$ permanece constante, de modo que por monotonía $u(c(K'), L) + beta E[B(K', omega')] <= u(c(h), L) + beta E[V_M^"stay" (h, omega')] <= V_M^"stay" (K, omega) = B(K, omega)$. Tomando $Psi = V$ y $W = V$ (o cualquier aproximación continua log-PWL $(B_"pwl", W_"pwl", Psi_"pwl")$ a distancia uniforme $epsilon.alt < (1 - beta) delta_0 \/ 16$ respecto de $(B, V, V)$, definiendo $tilde(B) := B_"pwl" + ((1 + beta)\/(1 - beta)) epsilon.alt$, $tilde(Psi) := Psi_"pwl" + ((1 + beta)\/(1 - beta)) epsilon.alt$ y $tilde(W) := W_"pwl" - ((1 + beta)\/(1 - beta)) epsilon.alt$, de modo que la suma positiva compensa el error uniforme en $tilde(B)$ y $tilde(Psi)$ y restar de $W_"pwl"$ restaura la desigualdad sub-Bellman en $tilde(W)$, garantizando exactamente ambas desigualdades mientras $inf_(cal(X)_M) (tilde(W) - tilde(B)) >= delta_0 - (4\/(1 - beta)) epsilon.alt > (3\/4) delta_0 > 0$), basta elegir $T_0$ con $beta^(T_0) sup(tilde(Psi) - tilde(B)) <= delta_0 \/ 2$ para asegurar $epsilon.alt_0 > 0$.
]

Antes de construir los certificados continuos, resolvemos el equilibrio exacto mediante VFI estocástica continua por sección áurea en ambos regímenes (Tabla 5 y Figura 3a), revelando una dicotomía económica nítida:
- *Bajo riesgo de ruina irreversible:* Un incremento en $p in [0\%, 8.0\%]$ reduce directamente el factor de descuento efectivo $tilde(beta)_p = beta(1 - p)$. Al desincentivarse el ahorro de largo plazo, la inversión cae ($K'(0.10)$ desciende de $0.13364$ a $0.12757$), el trabajo se contrae ($L$ cae de $0.6626$ a $0.6008$) y el umbral de trampa se dispara casi al triple: $S^"ruin" (p)$ sube de $0.001588$ ($p=0\%$) a $0.002013$ ($p=2\%$) y $0.004589$ ($p=8\%$, un salto de $2.89 times$).
- *Bajo recesión recuperable de Markov ($p_"rec" = 1\/3$):* Aunque la productividad adversa $A_B = 0.35 < A_G = 0.75$ eleva levemente los umbrales críticos ($S_G$ pasa de $0.001588$ a $0.001774$, apenas $+11.7\%$ en $p=8\%$, con $K_B^*$ bajando de $0.01086$ a $0.00991$), en el estado próspero $G$ la política óptima exhibe una *«huida hacia la seguridad» (_flight to safety_)*: tanto la inversión ($K'_G (0.10)$ sube de $0.13364$ a $0.13475$) como el esfuerzo laboral ($L_G$ sube de $0.6626$ a $0.6759$) aumentan precautoriamente para alejar el capital del abismo recesivo antes de que ocurra el choque adverso. En el Apéndice A.4 documentamos cómo este efecto precautorio se atenúa conforme sube $p_"rec"$ de $0.20$ a $0.50$.

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
  caption: [Tabla 5: Dicotomía en VFI estocástica continua: ruina absorbente frente a recesión recuperable de Markov ($p_"rec" = 1\/3$).],
)

== Caso 2: Bandas Continuas de Ruina sobre $p in [0\%, 2.0\%]$

#thm_box("Proposición", "3", [Certificado continuo en $60$ bandas de riesgo de ruina $p in [0\%, 2.0\%]$])[
  Consideremos la partición continua y contigua en $60$ sub-bandas del factor de descuento efectivo $tilde(beta)_p = beta (1 - p) in [0.950502, 0.9701]$, que recubre sin huecos todo $(beta, p) in [0.9699, 0.9701] times [0, 0.02]$. En cada una de las $60$ bandas $j = 0, dots, 59$, el motor CEGIS-LP puro certifica una tripleta $(Psi_j, W_j, B_("cegis", j))$ con $d_"ub,raw" <= 0$ sin desplazamientos aditivos, auditoría 3D de intervalos $d_"ub,iv" <= -0.000100$, monotonicidad en $M$ ($min W'_j >= m_G$), cotas de derivadas $< b$ y $< h$, y márgenes de salida adversa positivos en $M$, $H_1$ y $H_2 = [0.80, oo)$. Por el Corolario 3 (parte 1):
  1. En la banda superior ($p approx 0\%$, $tilde(beta)_p in [0.969732, 0.9701]$): el margen sobre $B_1$ es $+7.575$ con salidas adversas $M \/ H_1 \/ H_2 = +0.781 \/ +0.225 \/ +2.730$, plazo $T^*_(B_1) = 22$ y plazo comprimido $T^*_"CEGIS" = 6$.
  2. En todo el rectángulo extremo de riesgo $p = 2.0\%$ ($tilde(beta)_p in [0.950502, 0.950698]$, cubierto por las bandas $j = 0, dots, 5$), se certifica margen positivo sobre $B_1$ ($>= +0.0579$ en la esquina $j = 0$, con $T^*_(B_1) (2.0\%) = 93$, supervivencia $(0.98)^93 approx 15.3\%$) y plazo comprimido uniforme *$T^*_"CEGIS" in {5, 6}$* en las $60$ bandas ($T^*_"CEGIS" (2.0\%) = 5$ en la esquina inferior, elevando la supervivencia de Doob garantizada a *$(0.98)^5 = 90.4\%$*; Figura 3b).
]

Construimos una partición *continua y contigua de $60$ sub-bandas* sobre el factor de descuento efectivo $tilde(beta)_p = beta(1 - p) in [0.950502, 0.9701]$ cubriendo sin huecos todo el intervalo $(beta, p) in [0.9699, 0.9701] times [0, 0.02]$. *(Nota aclaratoria sobre invariancia a $V_"ruin"$: como en el Caso 2 el riesgo de ruina exógeno $p$ es independiente de $(K', L)$, la función valor bajo cualquier valor terminal finito $V_"ruin"$ satisface $V(K; V_"ruin") = V(K; 0) + (beta p V_"ruin")\/(1 - tilde(beta)_p)$, por lo que tanto la política óptima $(K'_t, L_t)$ como el umbral $S^"ruin" (p)$ y las cotas de supervivencia $(1-p)^(T^*)$ son exactamente invariantes a $V_"ruin"$, incluso cuando $V(K) < 0 = V_"ruin"$. Asimismo, en la esquina $j = 0$ ($p = 2.0\%$), resulta $T^*_"CEGIS" (2.0\%) = 5$ debido al menor ancho sub-banda de $tilde(beta)_p$ y a la mayor contracción $(0.9505)^T$.)*

#figure(
  image("fig3_stochastic_es.svg", width: 100%),
  caption: [Figura 3: (a) Dicotomía VFI estocástica: colapso de inversión bajo ruina exógena frente a «huida hacia la seguridad» en recesión de Markov ($p_"rec" = 1\/3$) y bajo ruina endógena $p(K) = p bold(1)_(K < 0.28)$ (Caso 5). (b) Probabilidad certificada de supervivencia $(1-p)^(T^*(p))$ en las $60$ bandas continuas de $tilde(beta)_p$ junto con la compresión acoplada de Markov ($E[tau] <= 38.8$, Caso 3).],
)

== Caso 3: Sistema Acoplado de Markov $(G, B)$, Compresión $(B_(G, theta), B_(B, theta))$ y $1 thin 054$ Hojas en $H_(1,B)$

#thm_box("Proposición", "4", [Supervivencia casi segura y compresión de tiempo medio esperado en Markov $(G, B)$])[
  Para el sistema acoplado de dos estados $(G, B)$ con transición adversa $p in {0\%, 0.5\%, 1.0\%, 1.5\%, 2.0\%, 5.0\%, 8.0\%, 12.0\%}$ y recuperación $p_"rec" = 1\/3$ sobre $tilde(cal(P))$, el motor CEGIS-LP acoplado certifica en todas las sub-bandas externas de $[beta_-, beta_+]$ y en las $32$ subcajas 3D ortogonales de $(A_G, A_B, q, eta)$ (desplegando en total *$1 thin 054$ hojas continuas* $(b, s)$ exportadas y re-auditadas independientemente):
  1. Márgenes afines de permanencia positivos ($"marg"_G >= 4.45$, $"marg"_B >= 0.84$, $T^*_G <= 34$, $T^*_B <= 88$), derivadas $< b$ y $< h$ en ambos estados, salidas adversas positivas en $M$ ($G >= +1.07$, $B >= +0.002$), $H_(1,G) >= +0.47$, $H_2 >= +3.02$, y salida adversa positiva en las $1 thin 054$ hojas continuas de $H_(1,B)$ ($m_(H_1,B,"32bx") >= +0.00015 > 0$).
  2. *Compresión acoplada CEGIS-LP de $(B_(G, theta), B_(B, theta))$:* Mientras la barrera afín analítica arrojaba cotas conservadoras de Doob de miles de períodos ($E[tau] <= 1 thin 480.3$ en $p=0\%$ y $13 thin 322.8$ en $p=12\%$), la síntesis conjunta de una pareja acoplada de barreras de permanencia $(B_(G, theta), B_(B, theta))$ reduce los plazos de transición por estado a $(T^*_G, T^*_B) = (5, 5)$ (y $(6, 6)$ en $p = 12\%$), multiplica la brecha de Doob en más de un orden de magnitud (*$epsilon.alt_0^"comp" in [0.3869, 0.4088]$* con $T_0^"opt" in {14, 15}$), y desploma la cota superior garantizada sobre el tiempo esperado de escape hasta *$E[tau] <= 35.1"–"38.8$ períodos* (compresión de $42 times$ a $343 times$; Teorema 7\* y Corolario 3).
]

La Tabla 6 reporta el peor caso entre las sub-bandas de $[beta_-, beta_+]$ y el mínimo sobre todas las $1 thin 054$ hojas continuas de $H_(1,B)$, comparando la base afín frente a la pareja comprimida $(B_(G, theta), B_(B, theta))$:

#figure(
  table(
    columns: (0.55fr, 0.85fr, 0.72fr, 0.90fr, 0.75fr, 0.82fr, 0.90fr, 0.90fr),
    inset: 4.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.0pt)[$p$],
      text(fill: white, weight: "bold", size: 8.0pt)[$(T_G, T_B)_"aff"$],
      text(fill: white, weight: "bold", size: 8.0pt)[$epsilon.alt_(0,"aff")$],
      text(fill: white, weight: "bold", size: 8.0pt)[$E[tau]_"aff"$],
      text(fill: white, weight: "bold", size: 8.0pt)[$(T_G^*, T_B^*)$],
      text(fill: white, weight: "bold", size: 8.0pt)[$epsilon.alt_0^"comp"$],
      text(fill: white, weight: "bold", size: 8.0pt)[$E[tau]_"comp"$],
      text(fill: white, weight: "bold", size: 8.0pt)[$H_(1,B,"32bx")$],
    ),
    [$0.0\%$], [$21, 45$], [$0.0331$], [$1 thin 480.3$], [$5, 5$], [$0.3988$], [*$35.1$*], [$+0.00017$],
    [$0.5\%$], [$22, 46$], [$0.0319$], [$1 thin 565.0$], [$5, 5$], [$0.3965$], [*$35.3$*], [$+0.00019$],
    [$1.0\%$], [$22, 47$], [$0.0306$], [$1 thin 665.0$], [$5, 5$], [$0.3952$], [*$35.4$*], [$+0.00015$],
    [$1.5\%$], [$22, 48$], [$0.0291$], [$1 thin 784.9$], [$5, 5$], [$0.3917$], [*$35.7$*], [$+0.00045$],
    [$2.0\%$], [$23, 49$], [$0.0276$], [$1 thin 920.7$], [$5, 5$], [$0.3917$], [*$35.7$*], [$+0.00196$],
    [$5.0\%$], [$26, 57$], [$0.0213$], [$2 thin 860.9$], [$5, 5$], [$0.4088$], [*$36.7$*], [$+0.00394$],
    [$8.0\%$], [$29, 67$], [$0.0151$], [$4 thin 688.6$], [$5, 5$], [$0.3989$], [*$37.6$*], [$+0.00903$],
    [$12.0\%$], [$34, 88$], [$0.0069$], [$13 thin 322.8$], [$6, 6$], [$0.3869$], [*$38.8$*], [$+0.00023$],
  ),
  caption: [Tabla 6: Compresión estocástica del Caso 3: barrera afín analítica frente a barreras acopladas CEGIS-LP $(B_(G, theta), B_(B, theta))$ ($T_0^"opt" in {14, 15}$), reduciendo $E[tau]$ de $13 thin 322.8$ a $38.8$ períodos en $p = 12\%$.],
)

== Caso 4: Transferibilidad al Régimen $A K$ Continuo por Tramos (Crecimiento Endógeno)

Como prueba concisa de transferibilidad hacia modelos de crecimiento endógeno sin ajuste manual de la arquitectura _CEGIS-PWL_, consideramos una especificación lineal por tramos en la cual a partir del umbral productivo $h = 0.28$ los rendimientos marginales del capital dejan de ser decrecientes y la producción adopta un régimen asintótico lineal $F_"AK" (K, L) = (K\/h) F_A (h, L)$ para todo $K >= h$ (preservando la tecnología CES de MR en $K < h$), con recursos disponibles totales $Y_"AK" (K, L) = q K + F_"AK" (K, L)$. Dado que el ingreso crece linealmente sin cota, el valor asintótico diverge logarítmicamente con pendiente límite exacta $D_"hi" = eta_+ \/ (1 - beta_+)$.

#thm_box("Proposición", "5", [Transferibilidad CEGIS-LP al régimen $A K$ continuo por tramos])[
  Bajo la tecnología híbrida CES--AK sobre la caja paramétrica $cal(P)$, el par $(Psi_"AK", W_"AK")$ ($196$ y $74$ nodos) sintetizado mediante CEGIS-LP ralo satisface $d_"ub,iv"^Psi = -0.000100 <= 0$ (auditado por el B&B 3D sobre $[10^(-4), 25.0]$ más colas analíticas en $(0, 10^(-4)]$ y $[25.0, oo)$ con B&B 1D sobre $L in [0, 1)$), $d_"ub,iv"^W = -2.66 times 10^(-6) <= 0$ (auditado sobre $[0.10, 3.5]$ más el rayo homogéneo exacto en $[3.5, oo)$ en `Decimal` de $50$ dígitos con $k'_"tail" = 5.6830 > 3.5$ y residual $-0.000250 <= 0$), interioridad estricta del ocio $omega^*(oo) = 0.9913 < 1$, e inexistencia de salidas adversas en todo $[0.28, oo)$:
  1. *Valores críticos en $h = 0.28$:* $Psi_"AK" (0.28) = +243.4645$ y $W_"AK" (0.28) = +238.1434$ (con $W_"AK" (0.10) = +209.7896$).
  2. *Plazo de escape comprimido:* Acotando con $B_theta$ y el par $(Psi_"AK", W_"AK")$, el tiempo máximo de tránsito en $M$ cae a *$T_"AK" = 4$* períodos ($inf_M (W - B_theta) = +266.1664$, $sup_M (Psi_"AK" - B_theta) = +295.9307$).
  3. *Auditoría completa de salidas adversas:* Mediante B&B 1D sobre $M$ y $[0.28, 3.5]$ más el rayo homogéneo analítico en $[3.5, oo)$ se certifican $m_(M,"iv") = +3.6786$, $m_(H_1,[0.28,3.5],"iv") = +3.5193$ y $m_(H_2,[3.5,oo),"iv") = +59.7121$, junto con holguras de derivada $< b$ de $+295.08$ y $< h$ de $+82.01$.
]

== Caso 5: Ruina Endógena Dependiente del Estado $p(K) = p bold(1)_(K < 0.28)$

A diferencia del Caso 2 (donde el riesgo de quiebra exógeno $p$ se cancela aditivamente mediante descuento efectivo $tilde(beta)_p$), modelamos aquí una economía en la que cruzar la escala segura $H = [0.28, oo)$ *elimina literalmente el riesgo existencial*: el peligro anual de ruina con valor de continuación $V_"ruin" = -60 < V(K)$ actúa únicamente sobre el estado vulnerable actual $K_t < 0.28$, obedeciendo la ecuación de Bellman explícita:
$ V(K) = max_((K', L)) { u(c, L) + beta [(1 - p(K)) V(K') + p(K) V_"ruin"] }, #h(12pt) p(K) = p bold(1)_(K < 0.28), #h(8pt) V_"ruin" = -60. $
(Nótese que la cota certificada de supervivencia $(1 - p)^(T^*)$ vale idénticamente tanto bajo exposición dependiente del estado actual $p(K_t)$ como del estado sucesor $p(K_(t+1))$.) Aparece entonces una prima endógena de supervivencia $V(K) - V_"ruin" >= 16.4 > 0$ que rompe la neutralidad de $V_"ruin"$ e induce una fuerte *«huida endógena hacia la seguridad»*: en la VFI continua de referencia (Tabla 7), al encenderse el riesgo endógeno ($p = 1\%$), la inversión óptima salta de $K'(0.10) = 0.13364$ a $0.13719$ ($+2.66\%$) y el trabajo sube de $0.6626$ a $0.7079$, acortando el tiempo óptimo de escape hacia $H$ de *$4$ a $3$ períodos* (Figura 3a).

#thm_box("Proposición", "6", [Certificación CEGIS-LP bajo ruina endógena $p(K) = p bold(1)_(K < 0.28)$ ($V_"ruin" = -60$)])[
  Para todo $p in {1\%, 2\%, 5\%, 8\%}$ sobre la caja paramétrica completa $cal(P)$, el motor CEGIS-LP certifica sin desplazamientos aditivos el techo global $Psi$ ($d_"ub,iv"^Psi <= -0.000100$), los testigos diferenciados $(W_M, W_H)$ por debajo y por encima de $h = 0.28$, la barrera de permanencia $B_theta$ ($d_"ub,iv"^B <= -0.000200$), derivadas $< b$ y $< h$, y márgenes positivos de salida adversa en $M$, $H_1$ y $H_2$:
  1. En los cuatro regímenes se certifica el plazo comprimido uniforme *$T^* = 5$* períodos, arrojando cotas garantizadas de supervivencia $(1 - p)^5$ (redondeadas estrictamente hacia abajo): $>= 95.09\%$ ($p=1\%$, exacto $0.950990$), $>= 90.39\%$ ($p=2\%$, exacto $0.903921$), $>= 77.37\%$ ($p=5\%$, exacto $0.773781$) y $>= 65.90\%$ ($p=8\%$, exacto $0.659082$).
  2. Todos los márgenes de salida adversa sobre el testigo permanecen estrictamente positivos hasta $p = 8\%$ ($M >= +0.4021$, $H_1 >= +0.3046$, $H_2 >= +2.8521$).
]

#v(0.2em)
#figure(
  table(
    columns: (0.65fr, 0.85fr, 0.85fr, 0.80fr, 0.65fr, 0.65fr, 0.90fr, 0.90fr, 0.95fr),
    inset: 4.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.0pt)[$p$],
      text(fill: white, weight: "bold", size: 8.0pt)[$S_"endo"$ (VFI)],
      text(fill: white, weight: "bold", size: 8.0pt)[$K'(0.10)$],
      text(fill: white, weight: "bold", size: 8.0pt)[$L(0.10)$],
      text(fill: white, weight: "bold", size: 8.0pt)[$tau_"VFI"$],
      text(fill: white, weight: "bold", size: 8.0pt)[$T^*$],
      text(fill: white, weight: "bold", size: 8.0pt)[$Pr("surv")$],
      text(fill: white, weight: "bold", size: 8.0pt)[Sal. $M$],
      text(fill: white, weight: "bold", size: 8.0pt)[$H_1 \/ H_2$],
    ),
    [$0.0\%$], [$0.001588$], [$0.13364$], [$0.6626$], [$4$], [---], [$100.0\%$], [---], [---],
    [$1.0\%$], [$0.001766$], [$0.13719$], [$0.7079$], [$3$], [$5$], [$>= 95.09\%$], [$+0.8004$], [$+0.305\/+2.852$],
    [$2.0\%$], [$0.002003$], [$0.13706$], [$0.7061$], [$3$], [$5$], [$>= 90.39\%$], [$+0.7518$], [$+0.305\/+2.852$],
    [$5.0\%$], [$0.002996$], [$0.13670$], [$0.7011$], [$3$], [$5$], [$>= 77.37\%$], [$+0.5752$], [$+0.305\/+2.852$],
    [$8.0\%$], [$0.004434$], [$0.13634$], [$0.6965$], [$3$], [$5$], [$>= 65.90\%$], [$+0.4021$], [$+0.305\/+2.852$],
  ),
  caption: [Tabla 7: Ruina endógena $p(K) = p bold(1)_(K < 0.28)$ con $V_"ruin" = -60$ (Caso 5): la VFI muestra huida endógena hacia $H$ ($tau_"VFI": 4 -> 3$) y CEGIS-LP certifica $T^* = 5$ en toda la caja $cal(P)$.],
)

== Caso 6: Pruebas de Estrés en Cajas Paramétricas Anchas (Hasta $10 times$)

La caja de referencia (7.3) de MR ($cal(P)$) posee un radio estrecho ($plus.minus 0.001$ en $A$, $plus.minus 0.0001$ en $beta, q, eta$). Para demostrar que el motor CEGIS-LP es un método general y no sobreajustado a un entorno puntual, ejecutamos pruebas de estrés en dos familias paramétricas ampliadas hasta $10 times$ su ancho en tasas e incertidumbre macroeconómica de $plus.minus 1.33\%$ en productividad: `MR_Box_7_1` ($A in [0.749, 0.751]$, $beta in [0.969, 0.971]$, $q in [0.919, 0.921]$, $eta in [0.699, 0.701]$) y `Macro_10x_Box` ($A in [0.740, 0.760]$, $beta in [0.969, 0.971]$, $q in [0.919, 0.921]$, $eta in [0.699, 0.701]$).

#thm_box("Proposición", "7", [Escalabilidad certificada de CEGIS-LP en cajas paramétricas anchas (Caso 6)])[
  Particionando `MR_Box_7_1` en $8$ subcajas ($2_beta times 2_q times 2_eta$) y `Macro_10x_Box` en $128$ subcajas ($16_A times 2_beta times 2_q times 2_eta$), CEGIS-LP sintetiza y re-audita por intervalos de manera completa en todas las subcajas una tripleta $(Psi, W, B_theta)$ satisfaciendo salidas adversas positivas en $M, H_1, H_2$, derivadas $< b \/ < h$, y plazo uniforme comprimido *$T_"full" = 6$* períodos (Tabla 8).
]

#v(0.2em)
#figure(
  table(
    columns: (1.25fr, 0.70fr, 1.45fr, 0.65fr, 0.80fr, 0.85fr, 0.85fr, 0.95fr),
    inset: 4.5pt,
    align: center,
    stroke: 0.45pt + luma(160),
    fill: (x, y) => if y == 0 { rgb("#0b2c4d") } else if calc.even(y) { rgb("#f6f9fc") } else { white },
    table.header(
      text(fill: white, weight: "bold", size: 8.0pt)[Caja Paramétrica],
      text(fill: white, weight: "bold", size: 8.0pt)[Subcajas],
      text(fill: white, weight: "bold", size: 8.0pt)[Rango $(A; beta, q, eta)$],
      text(fill: white, weight: "bold", size: 8.0pt)[$T_"full"$],
      text(fill: white, weight: "bold", size: 8.0pt)[Sal. $M$],
      text(fill: white, weight: "bold", size: 8.0pt)[$H_1 \/ H_2$],
      text(fill: white, weight: "bold", size: 8.0pt)[Síntesis],
      text(fill: white, weight: "bold", size: 8.0pt)[Re-verif.],
    ),
    [`MR_Box_7_1`], [$8$], [$[0.749, 0.751]$; $10 times$ tasas], [*$6$*], [$+0.5850$], [$+0.042\/+2.563$], [$29.9$ s], [$10.66$ s],
    [`Macro_10x_Box`], [$128$], [$[0.740, 0.760]$; $10 times$ tasas], [*$6$*], [$+0.5569$], [$+0.028\/+2.545$], [$745.7$ s], [$160.21$ s],
  ),
  caption: [Tabla 8: Prueba de estrés CEGIS-LP en cajas anchas (Caso 6). La columna Re-verif. reporta el tiempo medido del auditor independiente `audit_standalone.py`.],
)

// ============================================================================
// SECCIÓN 6: DISCUSIÓN Y ALCANCE
// ============================================================================
= Discusión, Alcance y Delimitación

La integración de barreras afines cerradas, análisis asintótico exacto, teoría converso-estocástica y síntesis determinista CEGIS-LP auditada sin `libm` transforma el enfoque FPBB en un esquema de demostración híbrido analítico-computacional libre de heurísticas sin cota. En particular, la separación estricta entre _Proposer_ (100% HiGHS-LP sin entrenamiento neuronal) y _Verifier_ asegura que la validez de cualquier resultado presentado en los Cuadros 1--8 sea independiente del algoritmo de síntesis: cualquier árbitro o lector puede verificar íntegramente el archivo compacto `cegis_certificates.json.xz` ($5.75$ MB, incluyendo las $60$ bandas del Caso 2, las $64$ bandas externas y las $1 thin 054$ hojas continuas de $H_(1,B)$ del Caso 3, las $16$ subcajas hasta $b_"ext" = 0.0030$, las barreras acopladas $(B_(G,theta), B_(B,theta))$, el Caso 4 AK, la ruina endógena del Caso 5 y las $136$ subcajas anchas del Caso 6) ejecutando el script auditor minimalista `audit_standalone.py` (329 líneas, cero dependencias de terceros y funciones trascendentes mediante Lema 11 de MR, con opción `--pure-python`), o ejecutando la verificación paralela completa `python verify_article_a.py --full-audit`.

Para preservar la unidad formal del trabajo en torno a planificación óptima con trabajo endógeno, leyes asintóticas de potencia y certificados estocásticos de Doob, nuestras extensiones de equilibrio descentralizado con fragmentación de firmas ($N_f$), la no monotonía institucional en forma de U bajo externalidades de escala (Teorema 10) y los regímenes de crecimiento balanceado de tipo _Red Queen_ (Proposición 3\*) constituyen el objeto específico de un estudio complementario (_Artículo B_).

// ============================================================================
// SECCIÓN 7: CONCLUSIONES
// ============================================================================
= Conclusiones

Hemos cerrado cinco extensiones de fondo sobre _Minimum Viable Scale_ de Milei y Reidel (octubre de 2026):
1. *Afilamiento determinista y cierre casi hasta $S_A$:* La barrera afín de un paso $B_1$ (_Teorema 9\*_) reduce exactamente a la mitad la cota analítica ($46 -> 23$), el análisis en $M_0$ fija $c < 0.25$ y afila $tau_(.1) <= 9$ uniformemente, el Wronskiano certifica salidas adversas (_Proposición 1\*\*_), CEGIS-LP comprime el plazo en $M$ a $T_theta = 9$ y $T_"full" = 5$ descomponiendo con cadenas no estacionarias la brecha frente a la malla ($T_"ns" (cal(P)) = 5 -> T_"ns" (theta_0) = 4 = tau_H^"VFI"$), y una cascada continua de $5$ etapas en $16$ subcajas cierra el $99.5\%$ de la brecha $[0.0025, 0.10)$ de la Figura 6 de MR ($98.6\%$ de $(S_A, 0.10)$, con $K_0 in [0.0030, 0.28) ==> T_"total" <= 52$).
2. *Resolución analítica pura asintótica y ley de segundo orden:* El _Teorema 3\*_ y el _Corolario 2\*_ demuestran la equivalencia límite $A^2 S_A^"fix" (1) -> A^2 S_A -> 0.000800$ para todo $beta theta > 1$, cierran por vía puramente analítica $S_A^"fix" (1) < S_A$ para todo $A$ grande mediante $T_M (A) = O(log log A)$, y formulan la ley asintótica heurística de segundo orden (_Observación 1_) validada mediante VFI hasta $A = 10^8$ con $L_"ss" = 7\/9$ y $Delta W_A^- = O(A^(-1))$.
3. *Completitud de Doob y Markov comprimido:* El _Teorema 7\*_ demuestra el converso estocástico exacto para FPBB de Doob, y las parejas acopladas $(B_(G,theta), B_(B,theta))$ comprimen la cota esperada de escape en Markov (Caso 3) hasta $p = 12\%$ de $E[tau] <= 1 thin 480"–"13 thin 323$ a *$35.1"–"38.8$ períodos* ($epsilon.alt_0^"comp" >= 0.3869$) con auditoría de las $1 thin 054$ hojas en $H_(1,B)$.
4. *Ruina invariante y ruina endógena $p(K)$:* Explicitamos la invariancia exacta respecto a $V_"ruin"$ en el Caso 2 ($60$ bandas, $T^*_"CEGIS" = 5$) e introducimos ruina endógena $p(K) = p bold(1)_(K < 0.28)$ (Caso 5), demostrando tanto la *huida endógena hacia la seguridad* en VFI ($tau_"VFI": 4 -> 3$) como certificados CEGIS-LP con $T^* = 5$.
5. *Estándar oro de verificación y escalabilidad:* Todo el motor es 100% HiGHS-LP determinista (cero PyTorch), utiliza `ln()` libre de `libm` por Lema 11 de MR, escala a cajas $10 times$ anchas (`Macro_10x_Box`, $128$ subcajas, $T_"full" = 6$), y se re-audita de forma independiente con `audit_standalone.py` (329 líneas, cero dependencias).

// ============================================================================
// APÉNDICE TÉCNICO A
// ============================================================================
#pagebreak()
= Apéndice Técnico

== Tabla A.1: Desambiguación Notacional

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
    [$Psi, W$], [Techo (super-barrera) y testigo factible], [Funciones continuas log-PWL certificadas en todo $(0, oo)$],
    [$cal(P)$], [Caja compacta de parámetros], [$A in [0.749, 0.751]$, $q in [0.9199, 0.9201]$, $beta in [0.9699, 0.9701]$, $eta in [0.6999, 0.7001]$],
    [$S_A, S_A^"fix" (overline(L))$], [Umbrales de Skiba endógeno y fijo], [Prueba pura $S_A^"fix" (1) < S_A$; 2.º orden $Delta_k$ ($beta theta > 1$)],
    [$Delta W_A^(pi^+), Delta W_A^+$], [Diferenciales variacionales en $S_A$], [Escala $beta^(T_M) g_(T_M) >> A^(-1)$ ($T_M = O(log log A)$)],
    [$p, p_"rec", p(K)$], [Riesgo de ruina, Markov y endógeno], [Ruina: $[0, 2\%]$; Markov: $p <= 12\%$; Endóg.: $p bold(1)_(K<0.28)$],
    [$epsilon.alt_0, E[tau]_"comp"$], [Brecha de Doob y cota Markov], [$epsilon.alt_0^"comp" >= 0.3869$; $E[tau] <= 35.1"–"38.8$ en $(B_(G,theta), B_(B,theta))$],
  ),
  caption: [Tabla A.1: Desambiguación notacional utilizada en el Artículo A.],
)

== Apéndice A.2: Fórmulas Explícitas de $E^+$ y Criterio de Wronskiano (Prop. 1\*\*)

Para que el artículo sea completamente autocontenido sin remitir al Apéndice F.3 de MR, explicitamos las fórmulas de salida adversa. Dada la producción CES $F_A (K, l_0) = A (2 K l_0 \/ (K + l_0))^(3\/2)$ en nivel laboral fijo $l_0$, se definen el valor marginal del trabajo $t(K) = partial F_(A_+) \/ partial L (K, l_0)$, su primera derivada en $K$, $t'(K) = t(K) dot 5 l_0 \/ (2 K (K + l_0))$, el recurso virtual mayorante $cal(S)(K) = q_+ K + F_(A_+) (K, l_0) + (1 - l_0) t(K)$, el excedente de consumo $c_"sup" (K) = cal(S)(K) - a$, el consumo del testigo $c_X (K) = q_- K + F_(A_-) (K, l_X) - s_X$, y la demanda óptima de ocio restringida $omega^*(K, eta) = min{1, (1 - eta) c_"sup" (K) \/ t(K)}$. El verificador de intervalos evalúa tanto la identidad exacta interior cuando $omega^* < 1$ en todo el subintervalo como el término envolvente completo $-eta thin t'(K) omega^* \/ c_"opt"$ cuando $omega^*$ puede alcanzar $1$, y certifica que el Wronskiano exacto del cociente $R_X (K) = (cal(S)(K) - a)\/c_X (K)$, dado por
$ Q_X (K) = cal(S)'(K) c_X (K) - c'_X (K) (cal(S)(K) - a), #h(12pt) Q'_X (K) = cal(S)''(K) c_X (K) - c''_X (K) (cal(S)(K) - a), $
mantiene $Q_X (K) < 0$, $Delta'_X (K) > 0$ y $Delta''_X (K) < 0$ en todo $[0.10, 0.28]$ y $[0.28, 0.80]$.

== Apéndice A.3: Protocolo Reproducible, Logaritmo sin `libm` y Auditor Autocontenido

El paquete de software reproducible (`audit_standalone.py`, `cegis_synth.py`, `cegis_verifier.py`, `interval_audit.py`, `pwl_model.py`, `verify_article_a.py`, `generate_figures.py` y `rust_verifier/`) prescinde íntegramente de PyTorch/Adam y reproduce deterministamente (`seed = 42`) los $6$ casos, las tablas, los certificados y las figuras (#link("https://github.com/lordtiva/mvs-bellman-barriers")[`github.com/lordtiva/mvs-bellman-barriers`]):
1. *Propuesta determinista HiGHS-LP (_Proposer_):* Todas las síntesis en los Casos 1--6 se formulan como programas lineales dispersos en SciPy/HiGHS (`_eval_pwl_basis_sparse`) paralelizados sobre subcajas y bandas.
2. *Aritmética de intervalos libre de `libm` (Lema 11 de MR):* Para eliminar cualquier dependencia en la implementación `libm` del sistema operativo (`f64::ln` o `Decimal.ln`), tanto el núcleo Rust (`iv_ln_pt` en `rust_verifier/src/lib.rs`, compilado en `mvs_verifier.dll` mediante `python rust_verifier/build.py`) como el módulo `Decimal` de 50 dígitos (`interval_audit.py`) calculan envolturas rigurosas de $log x$ reduciendo el argumento al rango $[1, 2)$ mediante potencias de $2$ y raíces cuadradas acotadas más serie truncada de $2 "atanh"((m-1)\/(m+1))$ con cota geométrica explícita de residuo (anchura máxima certificada $<= 10^(-47)$ en `Decimal` y $<= 2$ ULPs en IEEE-754 con signos acoplados de $beta$).
3. *Auditor minimalista de cero dependencias (`audit_standalone.py`):* El repositorio incluye un verificador puro de `329` líneas que únicamente importa módulos estándar de Python (`argparse`, `bisect`, `ctypes`, `concurrent.futures`, `decimal`, `json`, `lzma`, `math`, `os`, `time` — cero SciPy, HiGHS, NumPy o PyTorch), lee el archivo autocontenido `cegis_certificates.json.xz` ($5.754$ MB, conteniendo el $100\%$ de los certificados de los Casos 1--6, incluidas las $16$ subcajas near-Skiba, cadenas $\{J_k\}$, las $60$ bandas de ruina, las $64$ bandas externas acopladas de Markov más las $1 thin 054$ hojas de $H_(1,B)$, el Caso 4 AK, el Caso 5 de ruina endógena y las $136$ subcajas anchas del Caso 6) y soporta tanto el núcleo compilado en Rust como modo 100% Python (`--pure-python`, verificado en el Caso 4 en $75.01$ s). Ejecutando `python audit_standalone.py cegis_certificates.json.xz` se re-audita independientemente el Caso 1 en $49.80$ s, el Caso 2 en $7.81$ s, el Caso 3 en $2 thin 013.02$ s, el Caso 4 en $65.80$ s, el Caso 5 en $35.80$ s y el Caso 6 en $170.88$ s (`MR_Box_7_1` en $10.66$ s y `Macro_10x_Box` en $160.21$ s).

== Apéndice A.4: Sensibilidad a la Probabilidad de Recuperación $p_"rec"$ (Tabla A.4 parcial)

La Tabla A.4 presenta las tres filas de sensibilidad de la VFI estocástica continua de Markov en $p = 8.0\%$ al variar la probabilidad anual de recuperación $p_"rec"$ entre $0.20$ y $0.50$: cuanto menor es $p_"rec"$ (recesiones más persistentes), más fuerte es el incentivo precautorio de «huida hacia la seguridad» ($K'_G (0.10)$ sube de $0.13447$ a $0.13511$ y $L_G$ sube de $0.6726$ a $0.6803$).

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
  caption: [Tabla A.4 (extracto VFI Markov): Sensibilidad respecto a $p_"rec"$ evaluada en $p = 8.0\%$.],
)

// ============================================================================
// REFERENCIAS BIBLIOGRÁFICAS
// ============================================================================
#v(0.8em)
#heading(numbering: none)[Referencias]
#set text(size: 9.4pt)

- Abate, A., Ahmed, D., Giacobbe, M., & Peruffo, A. (2021). Formal synthesis of Lyapunov neural networks. _IEEE Control Systems Letters_, 5(3), 773--778.
- Acemoglu, D. (2009). _Introduction to Modern Economic Growth_. Princeton University Press.
- Akao, K., Ishii, H., Kamihigashi, T., & Nishimura, K. (2022). Existence of an optimal path in a continuous-time nonconcave Ramsey model. _Pure and Applied Functional Analysis_, 7(6), 1939--1952.
- Akao, K., Kamihigashi, T., & Nishimura, K. (2011). Monotonicity and continuity of the critical capital stock in the Dechert--Nishimura model. _Journal of Mathematical Economics_, 47(6), 677--682.
- Aubin, J.-P. (1991). _Viability Theory_. Birkhäuser.
- Dechert, W. D., & Nishimura, K. (1983). A complete characterization of optimal growth paths in an aggregated model with a non-concave production function. _Journal of Economic Theory_, 31(2), 332--354.
- Doob, J. L. (1953). _Stochastic Processes_. Wiley.
- Hernández-Lerma, O., & Lasserre, J. B. (1996). _Discrete-Time Markov Control Processes: Basic Optimality Criteria_. Springer.
- Huangfu, Q., & Hall, J. A. J. (2018). Parallelizing the dual revised simplex method. _Mathematical Programming Computation_, 10, 119--142.
- Kamihigashi, T., & Roy, S. (2007). A nonsmooth, nonconvex model of optimal growth. _Journal of Economic Theory_, 132(1), 435--460.
- Kraay, A., & McKenzie, D. (2014). Do poverty traps exist? Assessing the evidence. _Journal of Economic Perspectives_, 28(3), 127--148.
- Majumdar, M., & Mitra, T. (1982). Intertemporal allocation with a non-convex technology: The aggregative framework. _Journal of Economic Theory_, 27(1), 101--136.
- Milei, J., & Reidel, D. (2026). _Minimum Viable Scale: Bellman Barriers and the Economics of Survival_ (edición de octubre de 2026; posteriormente revisada como _Extinction and Escape under Increasing Returns_, noviembre de 2026). Manuscrito de trabajo (`minscale.org/paper/mvs.pdf`).
- Milgrom, P., & Segal, I. (2002). Envelope theorems for arbitrary choice sets. _Econometrica_, 70(2), 583--601.
- Moore, R. E., Kearfott, R. B., & Cloud, M. J. (2009). _Introduction to Interval Analysis_. SIAM.
- Ravanbakhsh, H., & Sankaranarayanan, S. (2019). Learning control Lyapunov functions from counterexamples and demonstrations. _Autonomous Robots_, 43, 275--307.
- Skiba, A. K. (1978). Optimal growth with a convex-concave production function. _Econometrica_, 46(3), 527--539.
- Solar-Lezama, A. (2008). _Program Synthesis by Sketching_. Tesis doctoral, UC Berkeley.
- Tucker, W. (2011). _Validated Numerics: A Short Introduction to Rigorous Computations_. Princeton University Press.
- Wagener, F. O. O. (2003). Skiba points and heteroclinic bifurcations, with applications to the shallow lake system. _Journal of Economic Dynamics and Control_, 27(9), 1533--1561.
- Williams, D. (1991). _Probability with Martingales_. Cambridge University Press.
