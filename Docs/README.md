## SUBSTRATE THEORY — FORMAL SPECIFICATION (LEAN 4 VERIFIED)
Matthew Scherf 2025

---

### TYPES

$\text{State} := \text{List Bool}$
$\text{Entity} : \text{opaque type}$
$\Omega : \text{Entity}$ (axiom)
$\text{Substrate} : \text{Entity}$ (axiom)
$\text{Time} := \mathbb{R}$
$\text{Phase} := \mathbb{R}$
$\text{Nbhd} := \text{List State}$
$\text{Precision} := \mathbb{N}$

$\text{KLZ.State} : \text{Type}$ (axiom)

---

### COMPLEXITY FUNCTIONS

$K : \text{Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{K\textunderscore sum} : \text{List Entity} \rightarrow \mathbb{R}$
$$\text{K\textunderscore sum}(es) := \sum_{e \in es} K(e)$$

$\text{K\textunderscore joint} : \text{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{K\textunderscore cond} : \text{Entity} \rightarrow \text{Entity} \rightarrow \mathbb{R}$
$$\text{K\textunderscore cond}(e_1,e_2) := \text{K\textunderscore joint}([e_1,e_2]) - K(e_1)$$

$C : \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{C\textunderscore sum} : \text{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\text{C\textunderscore sum}(es,p) := \sum_{e \in es} C(e,p)$$

$\text{C\textunderscore joint} : \text{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{C\textunderscore cond} : \text{Entity} \rightarrow \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\text{C\textunderscore cond}(e_1,e_2,p) := \text{C\textunderscore joint}([e_1,e_2],p) - C(e_1,p)$$

$\text{K\textunderscore LZ} : \text{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational)
$\text{K\textunderscore LZ} : \text{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module)

$\text{K\textunderscore toy} : \text{State} \rightarrow \mathbb{N}$
$$\text{K\textunderscore toy}(s) := |\text{dedup}(s)|$$

---

### RANK FUNCTIONS

$\text{rank\textunderscore K} : \text{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\text{rank\textunderscore C} : \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom)

---

### TEMPORAL FUNCTIONS

$\text{indexed} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity}$ (axiom)
$\text{temporal\textunderscore slice} : \text{List Entity} \rightarrow \text{Time} \rightarrow \text{List Entity}$
$\text{slice} : \text{List} (\text{Entity} \times \text{Time}) \rightarrow \text{Time} \rightarrow \text{List Entity}$

$\text{join} : \text{List State} \rightarrow \text{State}$ (axiom)
$\text{join} : \text{List KLZ.State} \rightarrow \text{KLZ.State}$ (axiom, KLZ module)

$\text{mode} : \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable axiom)

$\text{traj} : \text{Entity} \rightarrow \text{List} (\text{Entity} \times \text{Time})$
$$\text{traj}(e) := (\text{List.range 1000}).\text{map} (\lambda n. (\text{indexed } e \text{ } n, n))$$

$\text{P\textunderscore total} : \text{Entity} \rightarrow \mathbb{R}$
$$\text{P\textunderscore total}(e) := 1 \text{ (sum of uniform weights over trajectory)}$$

---

### COHERENCE FUNCTIONS

$\text{Coh} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{Coh\textunderscore op} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{Coh\textunderscore trajectory} : \text{Entity} \rightarrow \mathbb{R}$
$\text{dCoh\textunderscore dt} : \text{Entity} \rightarrow \text{Time} \rightarrow \mathbb{R}$ (noncomputable axiom)

$\text{compression\textunderscore ratio} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{R}$

---

### PARTITION FUNCTIONS

$\text{Z\textunderscore ideal} : \text{Finset Entity} \rightarrow \mathbb{R}$
$$\text{Z\textunderscore ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$

$\text{Z\textunderscore op} : \text{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\text{Z\textunderscore op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$

---

### GROUNDING FUNCTIONS

$\text{grounds} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{temporal\textunderscore grounds} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity} \rightarrow \text{Time} \rightarrow \text{Prop}$ (axiom)
$\text{bfs\textunderscore depth\textunderscore C} : \text{Entity} \rightarrow \mathbb{N} \rightarrow \text{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\text{bfs\textunderscore grounding\textunderscore path} : \text{Entity} \rightarrow \text{Finset Entity} \rightarrow \mathbb{N} \rightarrow \text{Option} (\text{List Entity})$

---

### PHYSICAL CONSTANTS

$c := 299792458 \text{ m/s}$
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
$t_{universe} : \mathbb{R}$ ($13.7 \times 10^9 < t_{universe} < 13.9 \times 10^9 \text{ years}$)

$N_e : \mathbb{R}$ ($50 < N_e < 70$, e-folds of inflation)
$n_s : \mathbb{R}$ ($0.96 < n_s < 0.97$, scalar spectral index)
$r_s : \mathbb{R}$ ($0 \leq r_s < 0.036$, tensor-to-scalar ratio)
$z_{transition} : \mathbb{R}$ ($0.6 < z_{transition} < 0.8$, matter-$\Lambda$ transition)

---

### GROUNDING CONSTANTS

$\text{c\textunderscore grounding} := 50 \text{ (bits)}$
$\text{c\textunderscore margin} := 5 \text{ (bits)}$

---

### KLZ CONSTANTS

$\text{c\textunderscore sub} : \mathbb{R} \text{ (constant)}$
$\text{c\textunderscore single} : \mathbb{R} \text{ (constant)}$
$\text{C\textunderscore mode} : \mathbb{R} \text{ (constant)}$
$\text{C\textunderscore coh} : \mathbb{R} \text{ (constant)}$

$\text{c\textunderscore time\textunderscore reduction} := \text{c\textunderscore sub} + \text{C\textunderscore mode}$
$\text{c\textunderscore time\textunderscore cohesion} := \text{c\textunderscore sub} + \text{C\textunderscore coh}$

---

### THRESHOLD PARAMETERS

$\text{measured\textunderscore inseparability\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\text{strong\textunderscore compression\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < \text{measured\textunderscore inseparability\textunderscore threshold}$)
$\text{temporal\textunderscore coherence\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\text{phase\textunderscore coupling\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$)
$\text{baseline\textunderscore maximal\textunderscore compression} : \mathbb{R}$ ($1 < \cdot$)

$\text{weak\textunderscore coupling\textunderscore threshold} : \mathbb{R}$
$\text{moderate\textunderscore coupling\textunderscore threshold} : \mathbb{R}$
$\text{strong\textunderscore coupling\textunderscore threshold} : \mathbb{R}$

**Hierarchy:**
$1 < \text{weak\textunderscore coupling\textunderscore threshold} < \text{moderate\textunderscore coupling\textunderscore threshold} < \text{strong\textunderscore coupling\textunderscore threshold} < \text{baseline\textunderscore maximal\textunderscore compression}$

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
$K(\text{Substrate}) = 0$
$K(\Omega) = 0$

#### G1 (Substrate Grounds All)
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow \text{is\textunderscore grounded}(e, \text{Substrate})$
$$\text{where } \text{is\textunderscore grounded}(e, \text{ctx}) := \text{K\textunderscore cond}(\text{ctx}, e) < K(e) - K(\text{ctx}) + \text{c\textunderscore grounding}$$

#### T7 (Time Arrow)
$\forall \text{hist, next.}$
$$\text{hist.length} \geq 2 \rightarrow$$
$$(\forall e \in \text{hist. is\textunderscore temporal\textunderscore presentation}(e)) \rightarrow$$
$$\text{is\textunderscore temporal\textunderscore presentation}(\text{next}) \rightarrow$$
$$\text{K\textunderscore joint}(\text{next}::\text{hist}) - \text{K\textunderscore joint}(\text{hist}) \leq \text{K\textunderscore joint}([\text{hist.last}, \text{hist.init}]) - K(\text{hist.init})$$

#### T4 (Emergence/Collapse)
$\forall e_{classical}, e_{quantum}.$
$$\text{is\textunderscore presentation}(e_{classical}) \rightarrow$$
$$\text{is\textunderscore quantum\textunderscore state}(e_{quantum}) \rightarrow$$
$$\text{emergent}(e_{classical}, e_{quantum}) \rightarrow$$
$$\text{is\textunderscore measurement\textunderscore device}(e_{classical}) \vee \text{is\textunderscore observable}(e_{classical})$$
$$\text{where } \text{emergent}(e_{classical}, e_{quantum}) := \text{K\textunderscore cond}(\text{Substrate}, e_{classical}) < K(e_{quantum})$$

#### C6 (Coherence Preservation)
$\forall e.$
$$\text{is\textunderscore quantum\textunderscore state}(e) \rightarrow \text{coherent}(e)$$
$$\text{where } \text{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$
$$\text{K\textunderscore cond}(\text{indexed}(e, t_1), \text{indexed}(e, t_2)) = \text{K\textunderscore cond}(\text{indexed}(e, t_2), \text{indexed}(e, t_1))$$

---

### AXIOM CONSEQUENCES

**substrate\_ultimate\_ground :**
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow \exists \text{path.}$
$$\text{path.head} = \text{Substrate} \wedge \text{path.last} = e \wedge$$
$$\forall i. i+1 < \text{path.length} \rightarrow \text{is\textunderscore grounded}(\text{path}[i+1], \text{path}[i])$$

**decoherence\_implies\_classical :**
$\forall e. \text{is\textunderscore presentation}(e) \wedge \neg\text{coherent}(e) \rightarrow$
$$\exists t_0. \forall t > t_0. \neg\text{is\textunderscore quantum\textunderscore state}(\text{indexed}(e, t))$$

**measurement\_breaks\_coherence :**
$\forall e_q, e_c.$
$$\text{is\textunderscore quantum\textunderscore state}(e_q) \wedge \text{coherent}(e_q) \wedge \text{emergent}(e_c, e_q) \rightarrow \neg\text{coherent}(e_c)$$

**indexed\_preserves\_presentation :**
$\forall e, t. \text{is\textunderscore presentation}(e) \rightarrow \text{is\textunderscore presentation}(\text{indexed}(e, t))$

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
$\forall e, \epsilon > 0.$
$$\text{is\textunderscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE2 (Uniform Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \text{is\textunderscore presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE3 (Probability Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \text{is\textunderscore presentation}(e)) \wedge \text{Z\textunderscore ideal}(S) > 0 \rightarrow$
$$\exists p_0. \forall p \geq p_0. \frac{|\text{Z\textunderscore op}(S, p) - \text{Z\textunderscore ideal}(S)|}{\text{Z\textunderscore ideal}(S)} < \epsilon$$

#### BRIDGE4 (Grounding Convergence)
$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \text{is\textunderscore presentation}(e_1) \wedge \text{is\textunderscore presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. \text{grounds\textunderscore K}(e_1, e_2) \leftrightarrow \text{grounds\textunderscore C}(e_1, e_2, p)$$
**where:**
$$\text{grounds\textunderscore K}(e_1, e_2) := \text{K\textunderscore cond}(e_1, e_2) < K(e_2) - K(e_1) + \text{c\textunderscore grounding}$$
$$\text{grounds\textunderscore C}(e_1, e_2, p) := \text{C\textunderscore cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \text{c\textunderscore grounding}$$

#### BRIDGE5 (Rank Stability)
$\forall S, e.$
$$e \in S \wedge \text{is\textunderscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. \text{rank\textunderscore C}(e, p) = \text{rank\textunderscore K}(e)$$

#### BRIDGE6 (Temporal Continuity)
$\forall e, \text{times}, \epsilon > 0. \text{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow$
$$\exists p_0. \forall p \geq p_0, t \in \text{times}. |\text{Coh\textunderscore op}([e], [t], p) - \text{Coh}([e], [t])| < \epsilon$$

#### BRIDGE7 (Conditional Convergence)
$\forall e_1, e_2, \epsilon > 0. \text{is\textunderscore presentation}(e_1) \wedge \text{is\textunderscore presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\text{C\textunderscore cond}(e_1, e_2, p) - \text{K\textunderscore cond}(e_1, e_2)| < \epsilon$$

#### BRIDGE7_joint (Joint Convergence)
$\forall es, \epsilon > 0. (\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\text{C\textunderscore joint}(es, p) - \text{K\textunderscore joint}(es)| < \epsilon$$

#### BRIDGE8 (Continuum Limit)
$\forall e, \text{times}, \epsilon > 0. \text{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow$
$$\exists p_0, \delta. \delta > 0 \wedge \forall p \geq p_0, t \in \text{times}.$$
$$\left| \frac{\text{Coh\textunderscore op}([e], [t+\delta], p) - \text{Coh\textunderscore op}([e], [t], p)}{\delta} - \text{dCoh\textunderscore dt}(e, t) \right| < \epsilon$$

---

### CA RULES

$F : \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable)
$\text{merge} : \text{KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable)

$\text{R\textunderscore Cohesion} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable axiom)
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
$\forall n, h.$
$$\text{coherent\textunderscore state}(\text{join}(n)) \rightarrow \text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) = \text{K\textunderscore LZ}(h)$$

**R\_G1\_grounding\_reduction**
$\forall n, h. \text{K\textunderscore LZ}(\text{join}(n)) > \text{c\textunderscore grounding} \rightarrow$
$$\text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$$

**R\_G1\_preserves\_time\_arrow**
$\forall \text{hist}, n, h.$
$$\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore G1}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time}$$
$$\text{where } \text{c\textunderscore time} := \max(\text{c\textunderscore time\textunderscore reduction}, \text{c\textunderscore time\textunderscore cohesion})$$

---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
$\forall e.$
$$\text{is\textunderscore presentation}(e) \rightarrow$$
$$(\text{has\textunderscore mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$
$$\text{energy\textunderscore of}(e) = \kappa_{energy} \cdot K(e)$$

#### G_Ψ (Grounding Stability)
$\forall e.$
$$\text{stable}(e) \leftrightarrow \text{K\textunderscore cond}(\Omega, e) > \text{c\textunderscore grounding}$$
$$\text{where } \text{stable}(e) := \text{is\textunderscore presentation}(e) \wedge \text{K\textunderscore cond}(\Omega, e) > \text{c\textunderscore grounding}$$

#### B_Ω (Holographic Bound)
$\forall \text{region, Area.}$
$$\text{is\textunderscore presentation}(\text{region}) \wedge \text{Area} > 0 \rightarrow K(\text{region}) \leq \frac{\text{Area}}{4\ell_{Planck}^2}$$

#### Ψ_I (Coherence Invariant)
$\forall e.$
$$\text{is\textunderscore temporal\textunderscore presentation}(e) \wedge \text{coherent}(e) \rightarrow \text{Coh\textunderscore trajectory}(e) \cdot \text{P\textunderscore total}(e) = 1$$

#### U_Ω (Uncertainty Principle)
$\forall e, \Delta K, \Delta t.$
$$\text{is\textunderscore temporal\textunderscore presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$

---

### RANK SYSTEM

$\text{rank\textunderscore K}(\Omega) = 0$
$\text{grounds}(e_1, e_2) \rightarrow \text{rank\textunderscore K}(e_2) < \text{rank\textunderscore K}(e_1)$
$\forall e. \exists n. \text{rank\textunderscore K}(e) = n$

$\text{rank\textunderscore C}(e, p) = \text{bfs\textunderscore depth\textunderscore C}(e, p, S) \text{ for } e \in S$

---

### UNIVERSAL GROUNDING

$\forall e. \text{is\textunderscore presentation}(e) \rightarrow \exists \text{path.}$
$$\text{path.head} = \Omega \wedge \text{path.last} = e \wedge$$
$$\forall i. i+1 < \text{path.length} \rightarrow \text{grounds}(\text{path}[i], \text{path}[i+1])$$

**grounding\_transitive :**
$\forall e_1, e_2, e_3.$
$$\text{grounds}(e_1, e_2) \wedge \text{grounds}(e_2, e_3) \rightarrow \text{grounds}(e_1, e_3)$$

**grounding\_acyclic :**
$\forall e. \neg\text{grounds}(e, e)$

---

### COMPLEXITY BOUNDS

$\text{K\textunderscore joint\textunderscore nonneg} : \forall es. 0 \leq \text{K\textunderscore joint}(es)$
$\text{K\textunderscore joint\textunderscore nil} : \text{K\textunderscore joint}([]) = 0$
$\text{K\textunderscore joint\textunderscore singleton} : \forall e. \text{K\textunderscore joint}([e]) = K(e)$

**compression\_axiom :**
$\forall es. (\forall e \in es. \text{is\textunderscore presentation}(e)) \wedge es.\text{length} \geq 2 \rightarrow$
$$\text{K\textunderscore joint}(es) < \text{K\textunderscore sum}(es)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow \text{K\textunderscore joint}(es) \leq \text{K\textunderscore sum}(es)$

**complexity\_positive :**
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow 0 < K(e)$

**substrate\_minimal :**
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow K(\text{Substrate}) \leq K(e)$

---

### OPERATIONAL BOUNDS

$\text{C\textunderscore nonneg} : \forall e, p. 0 \leq C(e, p)$
$\text{C\textunderscore monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$

$\text{C\textunderscore joint\textunderscore nonneg} : \forall es, p. 0 \leq \text{C\textunderscore joint}(es, p)$

$\text{K\textunderscore LZ\textunderscore nonneg} : \forall s. 0 \leq \text{K\textunderscore LZ}(s)$
$\text{K\textunderscore LZ\textunderscore empty} : \text{K\textunderscore LZ}(\text{join}([])) = 0$
$\text{K\textunderscore LZ\textunderscore monotone} : \forall s_1, s_2. s_1.\text{length} \leq s_2.\text{length} \rightarrow \text{K\textunderscore LZ}(s_1) \leq \text{K\textunderscore LZ}(s_2)$

---

### TOY COMPRESSOR BOUNDS

$\text{K\textunderscore toy\textunderscore lower\textunderscore bound} : \forall s. \text{K\textunderscore LZ}(s) \leq \text{K\textunderscore toy}(s)$
$\text{K\textunderscore toy\textunderscore upper\textunderscore bound} : \forall s. \text{K\textunderscore toy}(s) \leq \text{K\textunderscore LZ}(s) + \log_2(s.\text{length})$

---

### KLZ AXIOMS

**K\_LZ\_subadditive\_cons :**
$\forall x, xs. \text{K\textunderscore LZ}(\text{join}(x::xs)) \leq \text{K\textunderscore LZ}(\text{join}(xs)) + \text{K\textunderscore LZ}(x) + \text{c\textunderscore sub}$

**K\_LZ\_prefix :**
$\forall b, s. \text{K\textunderscore LZ}(\text{join}([b])) \leq \text{K\textunderscore LZ}(\text{join}(b::s))$

**K\_LZ\_singleton\_bound :**
$\forall b. \text{K\textunderscore LZ}(\text{join}([b])) \leq \text{c\textunderscore single}$

**K\_LZ\_mode\_le :**
$\forall s. \text{K\textunderscore LZ}(\text{mode}(s)) \leq \text{K\textunderscore LZ}(s) + \text{C\textunderscore mode}$

**K\_LZ\_mode\_absolute\_bound :**
$\forall s. \text{K\textunderscore LZ}(\text{mode}(s)) \leq \text{C\textunderscore mode}$

**C\_mode\_lt\_c\_grounding :**
$\text{C\textunderscore mode} < \text{c\textunderscore grounding}$

**K\_LZ\_cohesion\_bound\_raw :**
$\forall n, h. \text{K\textunderscore LZ}(\text{R\textunderscore Cohesion}(n, h)) \leq \text{C\textunderscore coh}$

---

### TIME ARROW THEOREMS

**time\_arrow\_reduction :**
$\forall \text{hist}, n.$
$$\text{K\textunderscore LZ}(\text{join}(\text{mode}(\text{join}(n)) :: \text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore reduction}$$

**time\_arrow\_cohesion :**
$\forall \text{hist}, n, h.$
$$\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore Cohesion}(n, h) :: \text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore cohesion}$$

---

### COHERENCE BOUNDS

**coherence\_bounds :**
$\forall es, \text{times}.$
$$(\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow 0 \leq \text{Coh}(es, \text{times}) \wedge \text{Coh}(es, \text{times}) \leq 1$$

**compression\_ratio\_ge\_one :**
$\forall es, \text{times}.$
$$(\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow 1 \leq \text{compression\textunderscore ratio}(es, \text{times})$$

---

### ERROR BOUNDS

**error\_bound\_linear :**
$\exists c > 0. \forall e, p. \text{is\textunderscore presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p$$

**error\_bound\_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. \text{is\textunderscore presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p^\alpha$$

**error\_bound\_general :**
$\exists M > 0. \forall e, p. \text{is\textunderscore presentation}(e) \rightarrow$
$$|C(e, p) - K(e)| \leq M/(p+1)$$

---

### PHYSICS CORRESPONDENCES

$\text{energy\textunderscore of}(e) = \kappa_{energy} \cdot K(e)$
$\text{mass}(e) = \text{energy\textunderscore of}(e)/c^2$
$\text{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$

$\text{is\textunderscore quantum}(\text{nbhd}) := \text{K\textunderscore LZ}(\text{join}(\text{nbhd})) \leq \text{c\textunderscore grounding}$
$\text{is\textunderscore classical}(\text{nbhd}) := \text{K\textunderscore LZ}(\text{join}(\text{nbhd})) > \text{c\textunderscore grounding}$

---

### PREDICATES

$\text{is\textunderscore substrate} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore emergent} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore temporal\textunderscore presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore static\textunderscore presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore quantum\textunderscore state} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore measurement\textunderscore device} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\textunderscore observable} : \text{Entity} \rightarrow \text{Prop}$ (axiom)

$\text{phenomenal} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{has\textunderscore mass} : \text{Entity} \rightarrow \text{Prop}$ (axiom)

$\text{grounds} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{temporal\textunderscore grounds} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity} \rightarrow \text{Time} \rightarrow \text{Prop}$ (axiom)
$\text{interacts} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{inseparable} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{emerges\textunderscore from} : \text{Entity} \rightarrow \text{List Entity} \rightarrow \text{Prop}$ (axiom)
$\text{phase\textunderscore coupled} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Phase} \rightarrow \text{Prop}$ (axiom)

$\text{coherent} : \text{Entity} \rightarrow \text{Prop}$
$\text{decoherent} : \text{Entity} \rightarrow \text{Prop}$
$\text{stable} : \text{Entity} \rightarrow \text{Prop}$

$\text{is\textunderscore quantum} : \text{List State} \rightarrow \text{Prop}$
$\text{is\textunderscore classical} : \text{List State} \rightarrow \text{Prop}$
$\text{coherent\textunderscore state} : \text{KLZ.State} \rightarrow \text{Prop}$

$\text{is\textunderscore grounded} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$

---

### ENTITY CLASSIFICATION

**entity\_classification :**
$\forall e. (\text{is\textunderscore substrate}(e) \wedge e = \text{Substrate}) \vee \text{is\textunderscore presentation}(e) \vee \text{is\textunderscore emergent}(e)$

$\text{substrate\textunderscore not\textunderscore presentation} : \forall e. \neg(\text{is\textunderscore substrate}(e) \wedge \text{is\textunderscore presentation}(e))$
$\text{substrate\textunderscore not\textunderscore emergent} : \forall e. \neg(\text{is\textunderscore substrate}(e) \wedge \text{is\textunderscore emergent}(e))$
$\text{presentation\textunderscore not\textunderscore emergent} : \forall e. \neg(\text{is\textunderscore presentation}(e) \wedge \text{is\textunderscore emergent}(e))$

**presentation\_temporal\_or\_static :**
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow$
$$(\text{is\textunderscore temporal\textunderscore presentation}(e) \vee \text{is\textunderscore static\textunderscore presentation}(e)) \wedge$$
$$\neg(\text{is\textunderscore temporal\textunderscore presentation}(e) \wedge \text{is\textunderscore static\textunderscore presentation}(e))$$

---

### SUBSTRATE PROPERTIES

$\text{substrate\textunderscore unique} : \forall x, y. \text{is\textunderscore substrate}(x) \wedge \text{is\textunderscore substrate}(y) \rightarrow x = y$
$\text{substrate\textunderscore is\textunderscore Substrate} : \text{is\textunderscore substrate}(\text{Substrate})$
$\text{Omega\textunderscore is\textunderscore substrate} : \text{is\textunderscore substrate}(\Omega)$
$\text{Omega\textunderscore eq\textunderscore Substrate} : \Omega = \text{Substrate}$

---

### TEMPORAL PRESERVATION

**indexed\_preserves\_presentation :**
$\forall e, t. \text{is\textunderscore presentation}(e) \rightarrow \text{is\textunderscore presentation}(\text{indexed}(e, t))$

**temporal\_slice\_preserves\_presentation :**
$\forall es, t. (\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow$
$$(\forall e \in \text{temporal\textunderscore slice}(es, t). \text{is\textunderscore presentation}(e))$$

---

### ASSOCIATIVITY

**join\_associative :**
$\forall s_1, s_2, s_3. \text{join}([\text{join}([s_1, s_2]), s_3]) = \text{join}([s_1, \text{join}([s_2, s_3])])$

---

### VERIFIED THEOREMS

**energy\_from\_complexity :**
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow \text{has\textunderscore mass}(e) \rightarrow$
$$\exists m > 0. m = \text{energy\textunderscore of}(e)/c^2$$

**entropy\_from\_complexity :**
$\forall e. \text{is\textunderscore presentation}(e) \rightarrow \exists S.$
$$S = k_B \cdot \log(2) \cdot K(e)$$

**coherence\_participation\_invariant :**
$\forall e. \text{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow \text{coherent}(e) \rightarrow$
$$0 < \text{P\textunderscore total}(e) \wedge \text{Coh\textunderscore trajectory}(e) = 1/\text{P\textunderscore total}(e)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow \text{K\textunderscore joint}(es) \leq \text{K\textunderscore sum}(es)$

**complexity\_subadditive :**
$\forall e_1, e_2. \text{is\textunderscore presentation}(e_1) \rightarrow \text{is\textunderscore presentation}(e_2) \rightarrow$
$$\text{K\textunderscore joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$

**compression\_ratio\_ge\_one :**
$\forall es, \text{times}. (\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow$
$$1 \leq \text{Compression\textunderscore ratio}(es, \text{times})$$

**R\_G1\_preserves\_grounding :**
$\forall n. \text{K\textunderscore LZ}(\text{mode}(\text{join}(n))) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$

**time\_arrow\_reduction :**
$\forall \text{hist}, n. \text{K\textunderscore LZ}(\text{join}(\text{mode}(\text{join}(n))::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore reduction}$

**time\_arrow\_cohesion :**
$\forall \text{hist}, n, h. \text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore Cohesion}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore cohesion}$

**P3\_C6\_preservation :**
$\forall n, h. \text{coherent\textunderscore state}(\text{join}(n)) \rightarrow \text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) = \text{K\textunderscore LZ}(h)$

**R\_G1\_grounding\_reduction :**
$\forall n, h. \text{K\textunderscore LZ}(\text{join}(n)) > \text{c\textunderscore grounding} \rightarrow$
$$\text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$$

**R\_G1\_preserves\_time\_arrow :**
$\forall \text{hist}, n, h.$
$$\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore G1}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{Lz}(\text{hist})) + \max(\text{c\textunderscore time\textunderscore reduction}, \text{c\textunderscore time\textunderscore cohesion})$$

**planck\_units\_positive :**
$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$

**error\_bound\_exists :**
$\forall e, p. \text{is\textunderscore presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| \leq \epsilon.\text{absolute}$