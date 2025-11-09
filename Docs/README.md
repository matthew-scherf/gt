## SUBSTRATE THEORY — FORMAL SPECIFICATION (LEAN 4 VERIFIED)
Matthew Scherf 2025

---

### TYPES

$\{State} := \{List Bool}$
$\{Entity} : \{opaque type}$
$\Omega : \{Entity}$ (axiom)
$\{Substrate} : \{Entity}$ (axiom)
$\{Time} := \mathbb{R}$
$\{Phase} := \mathbb{R}$
$\{Nbhd} := \{List State}$
$\{Precision} := \mathbb{N}$

$\{KLZ.State} : \{Type}$ (axiom)

---

### COMPLEXITY FUNCTIONS

$K : \{Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{K\textunderscore sum} : \{List Entity} \rightarrow \mathbb{R}$
$$\{K\textunderscore sum}(es) := \sum_{e \in es} K(e)$$

$\{K\textunderscore joint} : \{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{K\textunderscore cond} : \{Entity} \rightarrow \{Entity} \rightarrow \mathbb{R}$
$$\{K\textunderscore cond}(e_1,e_2) := \{K\textunderscore joint}([e_1,e_2]) - K(e_1)$$

$C : \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{C\textunderscore sum} : \{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{C\textunderscore sum}(es,p) := \sum_{e \in es} C(e,p)$$

$\{C\textunderscore joint} : \{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{C\textunderscore cond} : \{Entity} \rightarrow \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{C\textunderscore cond}(e_1,e_2,p) := \{C\textunderscore joint}([e_1,e_2],p) - C(e_1,p)$$

$\{K\textunderscore LZ} : \{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational)
$\{K\textunderscore LZ} : \{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module)

$\{K\textunderscore toy} : \{State} \rightarrow \mathbb{N}$
$$\{K\textunderscore toy}(s) := |\{dedup}(s)|$$

---

### RANK FUNCTIONS

$\{rank\textunderscore K} : \{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\{rank\textunderscore C} : \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom)

---

### TEMPORAL FUNCTIONS

$\{indexed} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity}$ (axiom)
$\{temporal\textunderscore slice} : \{List Entity} \rightarrow \{Time} \rightarrow \{List Entity}$
$\{slice} : \{List} (\{Entity} \times \{Time}) \rightarrow \{Time} \rightarrow \{List Entity}$

$\{join} : \{List State} \rightarrow \{State}$ (axiom)
$\{join} : \{List KLZ.State} \rightarrow \{KLZ.State}$ (axiom, KLZ module)

$\{mode} : \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable axiom)

$\{traj} : \{Entity} \rightarrow \{List} (\{Entity} \times \{Time})$
$$\{traj}(e) := (\{List.range 1000}).\{map} (\lambda n. (\{indexed } e \{ } n, n))$$

$\{P\textunderscore total} : \{Entity} \rightarrow \mathbb{R}$
$$\{P\textunderscore total}(e) := 1 \{ (sum of uniform weights over trajectory)}$$

---

### COHERENCE FUNCTIONS

$\{Coh} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{Coh\textunderscore op} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{Coh\textunderscore trajectory} : \{Entity} \rightarrow \mathbb{R}$
$\{dCoh\textunderscore dt} : \{Entity} \rightarrow \{Time} \rightarrow \mathbb{R}$ (noncomputable axiom)

$\{compression\textunderscore ratio} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{R}$

---

### PARTITION FUNCTIONS

$\{Z\textunderscore ideal} : \{Finset Entity} \rightarrow \mathbb{R}$
$$\{Z\textunderscore ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$

$\{Z\textunderscore op} : \{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{Z\textunderscore op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$

---

### GROUNDING FUNCTIONS

$\{grounds} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{temporal\textunderscore grounds} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity} \rightarrow \{Time} \rightarrow \{Prop}$ (axiom)
$\{bfs\textunderscore depth\textunderscore C} : \{Entity} \rightarrow \mathbb{N} \rightarrow \{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\{bfs\textunderscore grounding\textunderscore path} : \{Entity} \rightarrow \{Finset Entity} \rightarrow \mathbb{N} \rightarrow \{Option} (\{List Entity})$

---

### PHYSICAL CONSTANTS

$c := 299792458 \{ m/s}$
$\hbar : \mathbb{R}$ (axiom, $\hbar > 0$)
$G : \mathbb{R}$ (axiom, $G > 0$)
$k_B : \mathbb{R}$ (axiom, $k_B > 0$)
$e : \mathbb{R}$ (axiom, $e > 0$)
$\epsilon_0 : \mathbb{R}$ (axiom, $\epsilon_0 > 0$)
$\alpha : \mathbb{R}$ (axiom, $1/138 < \alpha < 1/137$)

$\ell_{Planck} := \sqrt{\frac{\hbar G}{c^3}}$
$t_{Planck} := \frac{\ell_{Planck}}{c}$
$M_{Planck} := \sqrt{\frac{\hbar c}{G}}$
$E_{Planck} := M_{Planck} \cdot c^2$
$T_{Planck} := \frac{E_{Planck}}{k_B}$

$\kappa_{energy} := E_{Planck}$
$\hbar_{eff} : \mathbb{R}$ (axiom, $\hbar_{eff} > 0$)
$\epsilon_{geom} : \mathbb{R}$ (axiom, $\epsilon_{geom} > 0$)

---

### COSMOLOGICAL PARAMETERS

$H_0 : \mathbb{R}$ ($67 < H_0 < 74$)
$\Omega_m : \mathbb{R}$ ($0.3 < \Omega_m < 0.32$)
$\Omega_\Lambda : \mathbb{R}$ ($0.68 < \Omega_\Lambda < 0.70$)
$\Omega_r : \mathbb{R}$ ($0 < \Omega_r < 0.0001$)
$\Omega_k : \mathbb{R}$ ($|\Omega_k| < 0.01$)
$\Omega_{DM} : \mathbb{R}$ ($0.25 < \Omega_{DM} < 0.27$)
$\Omega_{baryon} : \mathbb{R}$ ($0.04 < \Omega_{baryon} < 0.05$)
$t_{universe} : \mathbb{R}$ ($13.7 \times 10^9 < t_{universe} < 13.9 \times 10^9 \{ years}$)

$N_e : \mathbb{R}$ ($50 < N_e < 70$, e-folds of inflation)
$n_s : \mathbb{R}$ ($0.96 < n_s < 0.97$, scalar spectral index)
$r_s : \mathbb{R}$ ($0 \leq r_s < 0.036$, tensor-to-scalar ratio)
$z_{transition} : \mathbb{R}$ ($0.6 < z_{transition} < 0.8$, matter-$\Lambda$ transition)

---

### GROUNDING CONSTANTS

$\{c\textunderscore grounding} := 50 \{ (bits)}$
$\{c\textunderscore margin} := 5 \{ (bits)}$

---

### KLZ CONSTANTS

$\{c\textunderscore sub} : \mathbb{R} \{ (constant)}$
$\{c\textunderscore single} : \mathbb{R} \{ (constant)}$
$\{C\textunderscore mode} : \mathbb{R} \{ (constant)}$
$\{C\textunderscore coh} : \mathbb{R} \{ (constant)}$

$\{c\textunderscore time\textunderscore reduction} := \{c\textunderscore sub} + \{C\textunderscore mode}$
$\{c\textunderscore time\textunderscore cohesion} := \{c\textunderscore sub} + \{C\textunderscore coh}$

---

### THRESHOLD PARAMETERS

$\{measured\textunderscore inseparability\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\{strong\textunderscore compression\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < \{measured\textunderscore inseparability\textunderscore threshold}$)
$\{temporal\textunderscore coherence\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\{phase\textunderscore coupling\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$)
$\{baseline\textunderscore maximal\textunderscore compression} : \mathbb{R}$ ($1 < \cdot$)

$\{weak\textunderscore coupling\textunderscore threshold} : \mathbb{R}$
$\{moderate\textunderscore coupling\textunderscore threshold} : \mathbb{R}$
$\{strong\textunderscore coupling\textunderscore threshold} : \mathbb{R}$

**Hierarchy:**
$1 < \{weak\textunderscore coupling\textunderscore threshold} < \{moderate\textunderscore coupling\textunderscore threshold} < \{strong\textunderscore coupling\textunderscore threshold} < \{baseline\textunderscore maximal\textunderscore compression}$

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
$K(\{Substrate}) = 0$
$K(\Omega) = 0$

#### G1 (Substrate Grounds All)
$\forall e. \{is\textunderscore presentation}(e) \rightarrow \{is\textunderscore grounded}(e, \{Substrate})$
$$\{where } \{is\textunderscore grounded}(e, \{ctx}) := \{K\textunderscore cond}(\{ctx}, e) < K(e) - K(\{ctx}) + \{c\textunderscore grounding}$$

#### T7 (Time Arrow)
$\forall \{hist, next.}$
$$\{hist.length} \geq 2 \rightarrow$$
$$(\forall e \in \{hist. is\textunderscore temporal\textunderscore presentation}(e)) \rightarrow$$
$$\{is\textunderscore temporal\textunderscore presentation}(\{next}) \rightarrow$$
$$\{K\textunderscore joint}(\{next}::\{hist}) - \{K\textunderscore joint}(\{hist}) \leq \{K\textunderscore joint}([\{hist.last}, \{hist.init}]) - K(\{hist.init})$$

#### T4 (Emergence/Collapse)
$\forall e_{classical}, e_{quantum}.$
$$\{is\textunderscore presentation}(e_{classical}) \rightarrow$$
$$\{is\textunderscore quantum\textunderscore state}(e_{quantum}) \rightarrow$$
$$\{emergent}(e_{classical}, e_{quantum}) \rightarrow$$
$$\{is\textunderscore measurement\textunderscore device}(e_{classical}) \vee \{is\textunderscore observable}(e_{classical})$$
$$\{where } \{emergent}(e_{classical}, e_{quantum}) := \{K\textunderscore cond}(\{Substrate}, e_{classical}) < K(e_{quantum})$$

#### C6 (Coherence Preservation)
$\forall e.$
$$\{is\textunderscore quantum\textunderscore state}(e) \rightarrow \{coherent}(e)$$
$$\{where } \{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$
$$\{K\textunderscore cond}(\{indexed}(e, t_1), \{indexed}(e, t_2)) = \{K\textunderscore cond}(\{indexed}(e, t_2), \{indexed}(e, t_1))$$

---

### AXIOM CONSEQUENCES

**substrate_ultimate_ground :**
$\forall e. \{is\textunderscore presentation}(e) \rightarrow \exists \{path.}$
$$\{path.head} = \{Substrate} \wedge \{path.last} = e \wedge$$
$$\forall i. i+1 < \{path.length} \rightarrow \{is\textunderscore grounded}(\{path}[i+1], \{path}[i])$$

**decoherence_implies_classical :**
$\forall e. \{is\textunderscore presentation}(e) \wedge \neg\{coherent}(e) \rightarrow$
$$\exists t_0. \forall t > t_0. \neg\{is\textunderscore quantum\textunderscore state}(\{indexed}(e, t))$$

**measurement_underscorebreaks_coherence :**
$\forall e_q, e_c.$
$$\{is\textunderscore quantum\textunderscore state}(e_q) \wedge \{coherent}(e_q) \wedge \{emergent}(e_c, e_q) \rightarrow \neg\{coherent}(e_c)$$

**indexed_preserves_presentation :**
$\forall e, t. \{is\textunderscore presentation}(e) \rightarrow \{is\textunderscore presentation}(\{indexed}(e, t))$

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
$\forall e, \epsilon > 0.$
$$\{is\textunderscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE2 (Uniform Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \{is\textunderscore presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE3 (Probability Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \{is\textunderscore presentation}(e)) \wedge \{Z\textunderscore ideal}(S) > 0 \rightarrow$
$$\exists p_0. \forall p \geq p_0. \frac{|\{Z\textunderscore op}(S, p) - \{Z\textunderscore ideal}(S)|}{\{Z\textunderscore ideal}(S)} < \epsilon$$

#### BRIDGE4 (Grounding Convergence)
$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \{is\textunderscore presentation}(e_1) \wedge \{is\textunderscore presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. \{grounds\textunderscore K}(e_1, e_2) \leftrightarrow \{grounds\textunderscore C}(e_1, e_2, p)$$
**where:**
$$\{grounds\textunderscore K}(e_1, e_2) := \{K\textunderscore cond}(e_1, e_2) < K(e_2) - K(e_1) + \{c\textunderscore grounding}$$
$$\{grounds\textunderscore C}(e_1, e_2, p) := \{C\textunderscore cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \{c\textunderscore grounding}$$

#### BRIDGE5 (Rank Stability)
$\forall S, e.$
$$e \in S \wedge \{is\textunderscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. \{rank\textunderscore C}(e, p) = \{rank\textunderscore K}(e)$$

#### BRIDGE6 (Temporal Continuity)
$\forall e, \{times}, \epsilon > 0. \{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow$
$$\exists p_0. \forall p \geq p_0, t \in \{times}. |\{Coh\textunderscore op}([e], [t], p) - \{Coh}([e], [t])| < \epsilon$$

#### BRIDGE7 (Conditional Convergence)
$\forall e_1, e_2, \epsilon > 0. \{is\textunderscore presentation}(e_1) \wedge \{is\textunderscore presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\{C\textunderscore cond}(e_1, e_2, p) - \{K\textunderscore cond}(e_1, e_2)| < \epsilon$$

#### BRIDGE7_joint (Joint Convergence)
$\forall es, \epsilon > 0. (\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\{C\textunderscore joint}(es, p) - \{K\textunderscore joint}(es)| < \epsilon$$

#### BRIDGE8 (Continuum Limit)
$\forall e, \{times}, \epsilon > 0. \{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow$
$$\exists p_0, \delta. \delta > 0 \wedge \forall p \geq p_0, t \in \{times}.$$
$$\left| \frac{\{Coh\textunderscore op}([e], [t+\delta], p) - \{Coh\textunderscore op}([e], [t], p)}{\delta} - \{dCoh\textunderscore dt}(e, t) \right| < \epsilon$$

---

### CA RULES

$F : \text{KLZ.State} \rightarrow \text{KLZ.State} \text{ (noncomputable)}$
$\text{merge} : \text{KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State} \text{ (noncomputable)}$

$\text{R\textunderscore Cohesion} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State} \text{ (noncomputable axiom)}$
$$\text{R\textunderscore Cohesion}(n, h) := \text{merge}(F(\text{join}(n)), h)$$

$\text{R\textunderscore Reduction} : \text{List KLZ.State} \rightarrow \text{KLZ.State}$
$$\text{R\textunderscore Reduction}(n) := \text{mode}(\text{join}(n))$$

$\text{R\textunderscore G1} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$
$$\text{R\textunderscore G1}(n, h) := \begin{cases} \text{R\textunderscore Cohesion}(n, h) & \text{if } \text{K\textunderscore LZ}(\text{join}(n)) \leq \text{c\textunderscore grounding} \\ \text{R\textunderscore Reduction}(n) & \text{otherwise} \end{cases}$$

$\text{coherent\textunderscore state} : \text{KLZ.State} \rightarrow \text{Prop}$
$$\text{coherent\textunderscore state}(s) := \text{K\textunderscore LZ}(s) \leq \text{c\textunderscore grounding}$$

---

### CA PRESERVATION THEOREMS

#### P3 (C6 Preservation)
$$\forall n, h. \text{coherent\textunderscore state}(\text{join}(n)) \rightarrow \text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) = \text{K\textunderscore LZ}(h)$$

**R\_G1\_grounding\_reduction**
$$\forall n, h. \text{K\textunderscore LZ}(\text{join}(n)) > \text{c\textunderscore grounding} \rightarrow \text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$$

**R\_G1\_preserves\_time\_arrow**
$$\forall \text{hist}, n, h. \text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore G1}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{Jjoin}(\text{hist})) + \text{c\textunderscore time}$$
$$\text{where } \text{c\textunderscore time} := \max(\text{c\textunderscore time\textunderscore reduction}, \text{c\textunderscore time\textunderscore cohesion})$$
---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
$\forall e.$
$$\{is\textunderscore presentation}(e) \rightarrow$$
$$(\{has\textunderscore mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$
$$\{energy\textunderscore of}(e) = \kappa_{energy} \cdot K(e)$$

#### G_Ψ (Grounding Stability)
$\forall e.$
$$\{stable}(e) \leftrightarrow \{K\textunderscore cond}(\Omega, e) > \{c\textunderscore grounding}$$
$$\{where } \{stable}(e) := \{is\textunderscore presentation}(e) \wedge \{K\textunderscore cond}(\Omega, e) > \{c\textunderscore grounding}$$

#### B_Ω (Holographic Bound)
$\forall \{region, Area.}$
$$\{is\textunderscore presentation}(\{region}) \wedge \{Area} > 0 \rightarrow K(\{region}) \leq \frac{\{Area}}{4\ell_{Planck}^2}$$

#### Ψ_I (Coherence Invariant)
$\forall e.$
$$\{is\textunderscore temporal\textunderscore presentation}(e) \wedge \{coherent}(e) \rightarrow \{Coh\textunderscore trajectory}(e) \cdot \{P\textunderscore total}(e) = 1$$

#### U_Ω (Uncertainty Principle)
$\forall e, \Delta K, \Delta t.$
$$\{is\textunderscore temporal\textunderscore presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$

---

### RANK SYSTEM

$\{rank\textunderscore K}(\Omega) = 0$
$\{grounds}(e_1, e_2) \rightarrow \{rank\textunderscore K}(e_2) < \{rank\textunderscore K}(e_1)$
$\forall e. \exists n. \{rank\textunderscore K}(e) = n$

$\{rank\textunderscore C}(e, p) = \{bfs\textunderscore depth\textunderscore C}(e, p, S) \{ for } e \in S$

---

### UNIVERSAL GROUNDING

$\forall e. \{is\textunderscore presentation}(e) \rightarrow \exists \{path.}$
$$\{path.head} = \Omega \wedge \{path.last} = e \wedge$$
$$\forall i. i+1 < \{path.length} \rightarrow \{grounds}(\{path}[i], \{path}[i+1])$$

**grounding_transitive :**
$\forall e_1, e_2, e_3.$
$$\{grounds}(e_1, e_2) \wedge \{grounds}(e_2, e_3) \rightarrow \{grounds}(e_1, e_3)$$

**grounding_acyclic :**
$\forall e. \neg\{grounds}(e, e)$

---

### COMPLEXITY BOUNDS

$\{K\textunderscore joint\textunderscore nonneg} : \forall es. 0 \leq \{K\textunderscore joint}(es)$
$\{K\textunderscore joint\textunderscore nil} : \{K\textunderscore joint}([]) = 0$
$\{K\textunderscore joint\textunderscore singleton} : \forall e. \{K\textunderscore joint}([e]) = K(e)$

**compression_axiom :**
$\forall es. (\forall e \in es. \{is\textunderscore presentation}(e)) \wedge es.\{length} \geq 2 \rightarrow$
$$\{K\textunderscore joint}(es) < \{K\textunderscore sum}(es)$$

**joint_le_sum :**
$\forall es. (\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow \{K\textunderscore joint}(es) \leq \{K\textunderscore sum}(es)$

**complexity_positive :**
$\forall e. \{is\textunderscore presentation}(e) \rightarrow 0 < K(e)$

**substrate_minimal :**
$\forall e. \{is\textunderscore presentation}(e) \rightarrow K(\{Substrate}) \leq K(e)$

---

### OPERATIONAL BOUNDS

$\{C\textunderscore nonneg} : \forall e, p. 0 \leq C(e, p)$
$\{C\textunderscore monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$

$\{C\textunderscore joint\textunderscore nonneg} : \forall es, p. 0 \leq \{C\textunderscore joint}(es, p)$

$\{K\textunderscore LZ\textunderscore nonneg} : \forall s. 0 \leq \{K\textunderscore LZ}(s)$
$\{K\textunderscore LZ\textunderscore empty} : \{K\textunderscore LZ}(\{join}([])) = 0$
$\{K\textunderscore LZ\textunderscore monotone} : \forall s_1, s_2. s_1.\{length} \leq s_2.\{length} \rightarrow \{K\textunderscore LZ}(s_1) \leq \{K\textunderscore LZ}(s_2)$

---

### TOY COMPRESSOR BOUNDS

$\{K\textunderscore toy\textunderscore lower\textunderscore bound} : \forall s. \{K\textunderscore LZ}(s) \leq \{K\textunderscore toy}(s)$
$\{K\textunderscore toy\textunderscore upper\textunderscore bound} : \forall s. \{K\textunderscore toy}(s) \leq \{K\textunderscore LZ}(s) + \log_2(s.\{length})$

---

### KLZ AXIOMS

**K_LZ_subadditive_cons :**
$\forall x, xs. \{K\textunderscore LZ}(\{join}(x::xs)) \leq \{K\textunderscore LZ}(\{join}(xs)) + \{K\textunderscore LZ}(x) + \{c\textunderscore sub}$

**K_LZ_prefix :**
$\forall b, s. \{K\textunderscore LZ}(\{join}([b])) \leq \{K\textunderscore LZ}(\{join}(b::s))$

**K_LZ_singleton_bound :**
$\forall b. \{K\textunderscore LZ}(\{join}([b])) \leq \{c\textunderscore single}$

**K_LZ_mode_le :**
$\forall s. \{K\textunderscore LZ}(\{mode}(s)) \leq \{K\textunderscore LZ}(s) + \{C\textunderscore mode}$

**K_LZ_mode_absolute_bound :**
$\forall s. \{K\textunderscore LZ}(\{mode}(s)) \leq \{C\textunderscore mode}$

**C_mode_lt_c_grounding :**
$\{C\textunderscore mode} < \{c\textunderscore grounding}$

**K_LZ_cohesion_bound_raw :**
$\forall n, h. \{K\textunderscore LZ}(\{R\textunderscore Cohesion}(n, h)) \leq \{C\textunderscore coh}$

---

### TIME ARROW THEOREMS

**time_arrow_rereduction :**
$\forall \{hist}, n.$
$$\{K\textunderscore LZ}(\{join}(\{mode}(\{join}(n)) :: \{hist})) \leq \{K\textunderscore LZ}(\{join}(\{hist})) + \{c\textunderscore time\textunderscore reduction}$$

**time_arrow_cohesion :**
$\forall \{hist}, n, h.$
$$\{K\textunderscore LZ}(\{join}(\{R\textunderscore Cohesion}(n, h) :: \{hist})) \leq \{K\textunderscore LZ}(\{join}(\{hist})) + \{c\textunderscore time\textunderscore cohesion}$$

---

### COHERENCE BOUNDS

**coherence_bounds :**
$\forall es, \{times}.$
$$(\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow 0 \leq \{Coh}(es, \{times}) \wedge \{Coh}(es, \{times}) \leq 1$$

**compression_ratio_ge_one :**
$\forall es, \{times}.$
$$(\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow 1 \leq \{compression\textunderscore ratio}(es, \{times})$$

---

### ERROR BOUNDS

**error_bound_linear :**
$\exists c > 0. \forall e, p. \{is\textunderscore presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p$$

**error_bound_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. \{is\textunderscore presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p^\alpha$$

**error_bound_general :**
$\exists M > 0. \forall e, p. \{is\textunderscore presentation}(e) \rightarrow$
$$|C(e, p) - K(e)| \leq M/(p+1)$$

---

### PHYSICS CORRESPONDENCES

$\{energy\textunderscore of}(e) = \kappa_{energy} \cdot K(e)$
$\{mass}(e) = \{energy\textunderscore of}(e)/c^2$
$\{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$

$\{is\textunderscore quantum}(\{nbhd}) := \{K\textunderscore LZ}(\{join}(\{nbhd})) \leq \{c\textunderscore grounding}$
$\{is\textunderscore classical}(\{nbhd}) := \{K\textunderscore LZ}(\{join}(\{nbhd})) > \{c\textunderscore grounding}$

---

### PREDICATES

$\{is\textunderscore substrate} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore emergent} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore temporal\textunderscore presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore static\textunderscore presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore quantum\textunderscore state} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore measurement\textunderscore device} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\textunderscore observable} : \{Entity} \rightarrow \{Prop}$ (axiom)

$\{phenomenal} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{has\textunderscore mass} : \{Entity} \rightarrow \{Prop}$ (axiom)

$\{grounds} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{temporal\textunderscore grounds} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity} \rightarrow \{Time} \rightarrow \{Prop}$ (axiom)
$\{interacts} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{inseparable} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{emerges\textunderscore from} : \{Entity} \rightarrow \{List Entity} \rightarrow \{Prop}$ (axiom)
$\{phase\textunderscore coupled} : \{Entity} \rightarrow \{Entity} \rightarrow \{Phase} \rightarrow \{Prop}$ (axiom)

$\{coherent} : \{Entity} \rightarrow \{Prop}$
$\{decoherent} : \{Entity} \rightarrow \{Prop}$
$\{stable} : \{Entity} \rightarrow \{Prop}$

$\{is\textunderscore quantum} : \{List State} \rightarrow \{Prop}$
$\{is\textunderscore classical} : \{List State} \rightarrow \{Prop}$
$\{coherent\textunderscore state} : \{KLZ.State} \rightarrow \{Prop}$

$\{is\textunderscore grounded} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$

---

### ENTITY CLASSIFICATION

**entity_classification :**
$\forall e. (\{is\textunderscore substrate}(e) \wedge e = \{Substrate}) \vee \{is\textunderscore presentation}(e) \vee \{is\textunderscore emergent}(e)$

$\{substrate\textunderscore not\textunderscore presentation} : \forall e. \neg(\{is\textunderscore substrate}(e) \wedge \{is\textunderscore presentation}(e))$
$\{substrate\textunderscore not\textunderscore emergent} : \forall e. \neg(\{is\textunderscore substrate}(e) \wedge \{is\textunderscore emergent}(e))$
$\{presentation\textunderscore not\textunderscore emergent} : \forall e. \neg(\{is\textunderscore presentation}(e) \wedge \{is\textunderscore emergent}(e))$

**presentation_temporal_or_static :**
$\forall e. \{is\textunderscore presentation}(e) \rightarrow$
$$(\{is\textunderscore temporal\textunderscore presentation}(e) \vee \{is\textunderscore static\textunderscore presentation}(e)) \wedge$$
$$\neg(\{is\textunderscore temporal\textunderscore presentation}(e) \wedge \{is\textunderscore static\textunderscore presentation}(e))$$

---

### SUBSTRATE PROPERTIES

$\{substrate\textunderscore unique} : \forall x, y. \{is\textunderscore substrate}(x) \wedge \{is\textunderscore substrate}(y) \rightarrow x = y$
$\{substrate\textunderscore is\textunderscore Substrate} : \{is\textunderscore substrate}(\{Substrate})$
$\{Omega\textunderscore is\textunderscore substrate} : \{is\textunderscore substrate}(\Omega)$
$\{Omega\textunderscore eq\textunderscore Substrate} : \Omega = \{Substrate}$

---

### TEMPORAL PRESERVATION

**indexed_preserves_presentation :**
$\forall e, t. \{is\textunderscore presentation}(e) \rightarrow \{is\textunderscore presentation}(\{indexed}(e, t))$

**temporal_slice_preserves_presentation :**
$\forall es, t. (\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow$
$$(\forall e \in \{temporal\textunderscore slice}(es, t). \{is\textunderscore presentation}(e))$$

---

### ASSOCIATIVITY

**join_associative :**
$\forall s_1, s_2, s_3. \{join}([\{join}([s_1, s_2]), s_3]) = \{join}([s_1, \{join}([s_2, s_3])])$

---

### VERIFIED THEOREMS

**energy_from_complexity :**
$\forall e. \{is\textunderscore presentation}(e) \rightarrow \{has\textunderscore mass}(e) \rightarrow$
$$\exists m > 0. m = \{energy\textunderscore of}(e)/c^2$$

**entropy_from_complexity :**
$\forall e. \{is\textunderscore presentation}(e) \rightarrow \exists S.$
$$S = k_B \cdot \log(2) \cdot K(e)$$

**coherence_participation_invariant :**
$\forall e. \{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow \{coherent}(e) \rightarrow$
$$0 < \{P\textunderscore total}(e) \wedge \{Coh\textunderscore trajectory}(e) = 1/\{P\textunderscore total}(e)$$

**joint_le_sum :**
$\forall es. (\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow \{K\textunderscore joint}(es) \leq \{K\textunderscore sum}(es)$

**complexity_subadditive :**
$\forall e_1, e_2. \{is\textunderscore presentation}(e_1) \rightarrow \{is\textunderscore presentation}(e_2) \rightarrow$
$$\{K\textunderscore joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$

**compression_ratio_ge_one :**
$\forall es, \{times}. (\forall e \in es. \{is\textunderscore presentation}(e)) \rightarrow$
$$1 \leq \{Compression\textunderscore ratio}(es, \{times})$$

**R_G1_preserves_grounding :**
$\forall n. \{K\textunderscore LZ}(\{mode}(\{join}(n))) < \{K\textunderscore LZ}(\{join}(n)) + \{c\textunderscore grounding}$

**time_arrow_reduction :**
$\forall \{hist}, n. \{K\textunderscore LZ}(\{join}(\{mode}(\{join}(n))::\{hist})) \leq \{K\textunderscore LZ}(\{join}(\{hist})) + \{c\textunderscore time\textunderscore reduction}$

**time_arrow_cohesion :**
$\forall \{hist}, n, h. \{K\textunderscore LZ}(\{join}(\{R\textunderscore Cohesion}(n, h)::\{hist})) \leq \{K\textunderscore LZ}(\{join}(\{hist})) + \{c\textunderscore time\textunderscore cohesion}$

**P3_C6_preservation :**
$\forall n, h. \{coherent\textunderscore state}(\{join}(n)) \rightarrow \{K\textunderscore LZ}(\{R\textunderscore G1}(n, h)) = \{K\textunderscore LZ}(h)$

**R_G1_grounding_reduction :**
$\forall n, h. \{K\textunderscore LZ}(\{join}(n)) > \{c\textunderscore grounding} \rightarrow$
$$\{K\textunderscore LZ}(\{R\textunderscore G1}(n, h)) < \{K\textunderscore LZ}(\{join}(n)) + \{c\textunderscore grounding}$$

**R_G1_preserves_time_arrow :**
$\forall \{hist}, n, h.$
$$\{K\textunderscore LZ}(\{join}(\{R\textunderscore G1}(n, h)::\{hist})) \leq \{K\textunderscore LZ}(\{join}(\{Lz}(\{hist})) + \max(\{c\textunderscore time\textunderscore reduction}, \{c\textunderscore time\textunderscore cohesion})$$

**planck_units_positive :**
$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$

**error_bound_exists :**
$\forall e, p. \{is\textunderscore presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| \leq \epsilon.\{absolute}$