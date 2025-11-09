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
$\{K\underscore sum} : \{List Entity} \rightarrow \mathbb{R}$
$$\{K\underscore sum}(es) := \sum_{e \in es} K(e)$$

$\{K\underscore joint} : \{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{K\underscore cond} : \{Entity} \rightarrow \{Entity} \rightarrow \mathbb{R}$
$$\{K\underscore cond}(e_1,e_2) := \{K\underscore joint}([e_1,e_2]) - K(e_1)$$

$C : \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{C\underscore sum} : \{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{C\underscore sum}(es,p) := \sum_{e \in es} C(e,p)$$

$\{C\underscore joint} : \{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{C\underscore cond} : \{Entity} \rightarrow \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{C\underscore cond}(e_1,e_2,p) := \{C\underscore joint}([e_1,e_2],p) - C(e_1,p)$$

$\{K\underscore LZ} : \{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational)
$\{K\underscore LZ} : \{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module)

$\{K\underscore toy} : \{State} \rightarrow \mathbb{N}$
$$\{K\underscore toy}(s) := |\{dedup}(s)|$$

---

### RANK FUNCTIONS

$\{rank\underscore K} : \{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\{rank\underscore C} : \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom)

---

### TEMPORAL FUNCTIONS

$\{indexed} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity}$ (axiom)
$\{temporal\underscore slice} : \{List Entity} \rightarrow \{Time} \rightarrow \{List Entity}$
$\{slice} : \{List} (\{Entity} \times \{Time}) \rightarrow \{Time} \rightarrow \{List Entity}$

$\{join} : \{List State} \rightarrow \{State}$ (axiom)
$\{join} : \{List KLZ.State} \rightarrow \{KLZ.State}$ (axiom, KLZ module)

$\{mode} : \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable axiom)

$\{traj} : \{Entity} \rightarrow \{List} (\{Entity} \times \{Time})$
$$\{traj}(e) := (\{List.range 1000}).\{map} (\lambda n. (\{indexed } e \{ } n, n))$$

$\{P\underscore total} : \{Entity} \rightarrow \mathbb{R}$
$$\{P\underscore total}(e) := 1 \{ (sum of uniform weights over trajectory)}$$

---

### COHERENCE FUNCTIONS

$\{Coh} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{Coh\underscore op} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{Coh\underscore trajectory} : \{Entity} \rightarrow \mathbb{R}$
$\{dCoh\underscore dt} : \{Entity} \rightarrow \{Time} \rightarrow \mathbb{R}$ (noncomputable axiom)

$\{compression\underscore ratio} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{R}$

---

### PARTITION FUNCTIONS

$\{Z\underscore ideal} : \{Finset Entity} \rightarrow \mathbb{R}$
$$\{Z\underscore ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$

$\{Z\underscore op} : \{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{Z\underscore op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$

---

### GROUNDING FUNCTIONS

$\{grounds} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{temporal\underscore grounds} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity} \rightarrow \{Time} \rightarrow \{Prop}$ (axiom)
$\{bfs\underscore depth\underscore C} : \{Entity} \rightarrow \mathbb{N} \rightarrow \{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\{bfs\underscore grounding\underscore path} : \{Entity} \rightarrow \{Finset Entity} \rightarrow \mathbb{N} \rightarrow \{Option} (\{List Entity})$

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

$\{c\underscore grounding} := 50 \{ (bits)}$
$\{c\underscore margin} := 5 \{ (bits)}$

---

### KLZ CONSTANTS

$\{c\underscore sub} : \mathbb{R} \{ (constant)}$
$\{c\underscore single} : \mathbb{R} \{ (constant)}$
$\{C\underscore mode} : \mathbb{R} \{ (constant)}$
$\{C\underscore coh} : \mathbb{R} \{ (constant)}$

$\{c\underscore time\underscore reduction} := \{c\underscore sub} + \{C\underscore mode}$
$\{c\underscore time\underscore cohesion} := \{c\underscore sub} + \{C\underscore coh}$

---

### THRESHOLD PARAMETERS

$\{measured\underscore inseparability\underscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\{strong\underscore compression\underscore threshold} : \mathbb{R}$ ($0 < \cdot < \{measured\underscore inseparability\underscore threshold}$)
$\{temporal\underscore coherence\underscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\{phase\underscore coupling\underscore threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$)
$\{baseline\underscore maximal\underscore compression} : \mathbb{R}$ ($1 < \cdot$)

$\{weak\underscore coupling\underscore threshold} : \mathbb{R}$
$\{moderate\underscore coupling\underscore threshold} : \mathbb{R}$
$\{strong\underscore coupling\underscore threshold} : \mathbb{R}$

**Hierarchy:**
$1 < \{weak\underscore coupling\underscore threshold} < \{moderate\underscore coupling\underscore threshold} < \{strong\underscore coupling\underscore threshold} < \{baseline\underscore maximal\underscore compression}$

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
$K(\{Substrate}) = 0$
$K(\Omega) = 0$

#### G1 (Substrate Grounds All)
$\forall e. \{is\underscore presentation}(e) \rightarrow \{is\underscore grounded}(e, \{Substrate})$
$$\{where } \{is\underscore grounded}(e, \{ctx}) := \{K\underscore cond}(\{ctx}, e) < K(e) - K(\{ctx}) + \{c\underscore grounding}$$

#### T7 (Time Arrow)
$\forall \{hist, next.}$
$$\{hist.length} \geq 2 \rightarrow$$
$$(\forall e \in \{hist. is\underscore temporal\underscore presentation}(e)) \rightarrow$$
$$\{is\underscore temporal\underscore presentation}(\{next}) \rightarrow$$
$$\{K\underscore joint}(\{next}::\{hist}) - \{K\underscore joint}(\{hist}) \leq \{K\underscore joint}([\{hist.last}, \{hist.init}]) - K(\{hist.init})$$

#### T4 (Emergence/Collapse)
$\forall e_{classical}, e_{quantum}.$
$$\{is\underscore presentation}(e_{classical}) \rightarrow$$
$$\{is\underscore quantum\underscore state}(e_{quantum}) \rightarrow$$
$$\{emergent}(e_{classical}, e_{quantum}) \rightarrow$$
$$\{is\underscore measurement\underscore device}(e_{classical}) \vee \{is\underscore observable}(e_{classical})$$
$$\{where } \{emergent}(e_{classical}, e_{quantum}) := \{K\underscore cond}(\{Substrate}, e_{classical}) < K(e_{quantum})$$

#### C6 (Coherence Preservation)
$\forall e.$
$$\{is\underscore quantum\underscore state}(e) \rightarrow \{coherent}(e)$$
$$\{where } \{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$
$$\{K\underscore cond}(\{indexed}(e, t_1), \{indexed}(e, t_2)) = \{K\underscore cond}(\{indexed}(e, t_2), \{indexed}(e, t_1))$$

---

### AXIOM CONSEQUENCES

**substrate\_ultimate\_ground :**
$\forall e. \{is\underscore presentation}(e) \rightarrow \exists \{path.}$
$$\{path.head} = \{Substrate} \wedge \{path.last} = e \wedge$$
$$\forall i. i+1 < \{path.length} \rightarrow \{is\underscore grounded}(\{path}[i+1], \{path}[i])$$

**decoherence\_implies\_classical :**
$\forall e. \{is\underscore presentation}(e) \wedge \neg\{coherent}(e) \rightarrow$
$$\exists t_0. \forall t > t_0. \neg\{is\underscore quantum\underscore state}(\{indexed}(e, t))$$

**measurement\_breaks\_coherence :**
$\forall e_q, e_c.$
$$\{is\underscore quantum\underscore state}(e_q) \wedge \{coherent}(e_q) \wedge \{emergent}(e_c, e_q) \rightarrow \neg\{coherent}(e_c)$$

**indexed\_preserves\_presentation :**
$\forall e, t. \{is\underscore presentation}(e) \rightarrow \{is\underscore presentation}(\{indexed}(e, t))$

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
$\forall e, \epsilon > 0.$
$$\{is\underscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE2 (Uniform Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \{is\underscore presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE3 (Probability Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \{is\underscore presentation}(e)) \wedge \{Z\underscore ideal}(S) > 0 \rightarrow$
$$\exists p_0. \forall p \geq p_0. \frac{|\{Z\underscore op}(S, p) - \{Z\underscore ideal}(S)|}{\{Z\underscore ideal}(S)} < \epsilon$$

#### BRIDGE4 (Grounding Convergence)
$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \{is\underscore presentation}(e_1) \wedge \{is\underscore presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. \{grounds\underscore K}(e_1, e_2) \leftrightarrow \{grounds\underscore C}(e_1, e_2, p)$$
**where:**
$$\{grounds\underscore K}(e_1, e_2) := \{K\underscore cond}(e_1, e_2) < K(e_2) - K(e_1) + \{c\underscore grounding}$$
$$\{grounds\underscore C}(e_1, e_2, p) := \{C\underscore cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \{c\underscore grounding}$$

#### BRIDGE5 (Rank Stability)
$\forall S, e.$
$$e \in S \wedge \{is\underscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. \{rank\underscore C}(e, p) = \{rank\underscore K}(e)$$

#### BRIDGE6 (Temporal Continuity)
$\forall e, \{times}, \epsilon > 0. \{is\underscore temporal\underscore presentation}(e) \rightarrow$
$$\exists p_0. \forall p \geq p_0, t \in \{times}. |\{Coh\underscore op}([e], [t], p) - \{Coh}([e], [t])| < \epsilon$$

#### BRIDGE7 (Conditional Convergence)
$\forall e_1, e_2, \epsilon > 0. \{is\underscore presentation}(e_1) \wedge \{is\underscore presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\{C\underscore cond}(e_1, e_2, p) - \{K\underscore cond}(e_1, e_2)| < \epsilon$$

#### BRIDGE7_joint (Joint Convergence)
$\forall es, \epsilon > 0. (\forall e \in es. \{is\underscore presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\{C\underscore joint}(es, p) - \{K\underscore joint}(es)| < \epsilon$$

#### BRIDGE8 (Continuum Limit)
$\forall e, \{times}, \epsilon > 0. \{is\underscore temporal\underscore presentation}(e) \rightarrow$
$$\exists p_0, \delta. \delta > 0 \wedge \forall p \geq p_0, t \in \{times}.$$
$$\left| \frac{\{Coh\underscore op}([e], [t+\delta], p) - \{Coh\underscore op}([e], [t], p)}{\delta} - \{dCoh\underscore dt}(e, t) \right| < \epsilon$$

---

### CA RULES

$F : \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable)
$\{merge} : \{KLZ.State} \rightarrow \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable)

$\{R\underscore Cohesion} : \{List KLZ.State} \rightarrow \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable axiom)
$$\{R\underscore Cohesion}(n, h) := \{merge}(F(\{join}(n)), h)$$

$\{R\underscore Reduction} : \{List KLZ.State} \rightarrow \{KLZ.State}$
$$\{R\underscore Reduction}(n) := \{mode}(\{join}(n))$$

$\{R\underscore G1} : \{List KLZ.State} \rightarrow \{KLZ.State} \rightarrow \{KLZ.State}$
$$\{R\underscore G1}(n, h) := \begin{cases} \{R\underscore Cohesion}(n, h) & \{if } \{K\underscore LZ}(\{join}(n)) \leq \{c\underscore grounding} \\ \{R\underscore Reduction}(n) & \{otherwise} \end{cases}$$

$\{coherent\underscore state} : \{KLZ.State} \rightarrow \{Prop}$
$$\{coherent\underscore state}(s) := \{K\underscore LZ}(s) \leq \{c\underscore grounding}$$

---

### CA PRESERVATION THEOREMS

#### P3 (C6 Preservation)
$\forall n, h.$
$$\{coherent\underscore state}(\{join}(n)) \rightarrow \{K\underscore LZ}(\{R\underscore G1}(n, h)) = \{K\underscore LZ}(h)$$

**R\_G1\_grounding\_reduction**
$\forall n, h. \{K\underscore LZ}(\{join}(n)) > \{c\underscore grounding} \rightarrow$
$$\{K\underscore LZ}(\{R\underscore G1}(n, h)) < \{K\underscore LZ}(\{join}(n)) + \{c\underscore grounding}$$

**R\_G1\_preserves\_time\_arrow**
$\forall \{hist}, n, h.$
$$\{K\underscore LZ}(\{join}(\{R\underscore G1}(n, h)::\{hist})) \leq \{K\underscore LZ}(\{join}(\{hist})) + \{c\underscore time}$$
$$\{where } \{c\underscore time} := \max(\{c\underscore time\underscore reduction}, \{c\underscore time\underscore cohesion})$$

---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
$\forall e.$
$$\{is\underscore presentation}(e) \rightarrow$$
$$(\{has\underscore mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$
$$\{energy\underscore of}(e) = \kappa_{energy} \cdot K(e)$$

#### G_Ψ (Grounding Stability)
$\forall e.$
$$\{stable}(e) \leftrightarrow \{K\underscore cond}(\Omega, e) > \{c\underscore grounding}$$
$$\{where } \{stable}(e) := \{is\underscore presentation}(e) \wedge \{K\underscore cond}(\Omega, e) > \{c\underscore grounding}$$

#### B_Ω (Holographic Bound)
$\forall \{region, Area.}$
$$\{is\underscore presentation}(\{region}) \wedge \{Area} > 0 \rightarrow K(\{region}) \leq \frac{\{Area}}{4\ell_{Planck}^2}$$

#### Ψ_I (Coherence Invariant)
$\forall e.$
$$\{is\underscore temporal\underscore presentation}(e) \wedge \{coherent}(e) \rightarrow \{Coh\underscore trajectory}(e) \cdot \{P\underscore total}(e) = 1$$

#### U_Ω (Uncertainty Principle)
$\forall e, \Delta K, \Delta t.$
$$\{is\underscore temporal\underscore presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$

---

### RANK SYSTEM

$\{rank\underscore K}(\Omega) = 0$
$\{grounds}(e_1, e_2) \rightarrow \{rank\underscore K}(e_2) < \{rank\underscore K}(e_1)$
$\forall e. \exists n. \{rank\underscore K}(e) = n$

$\{rank\underscore C}(e, p) = \{bfs\underscore depth\underscore C}(e, p, S) \{ for } e \in S$

---

### UNIVERSAL GROUNDING

$\forall e. \{is\underscore presentation}(e) \rightarrow \exists \{path.}$
$$\{path.head} = \Omega \wedge \{path.last} = e \wedge$$
$$\forall i. i+1 < \{path.length} \rightarrow \{grounds}(\{path}[i], \{path}[i+1])$$

**grounding\_transitive :**
$\forall e_1, e_2, e_3.$
$$\{grounds}(e_1, e_2) \wedge \{grounds}(e_2, e_3) \rightarrow \{grounds}(e_1, e_3)$$

**grounding\_acyclic :**
$\forall e. \neg\{grounds}(e, e)$

---

### COMPLEXITY BOUNDS

$\{K\underscore joint\underscore nonneg} : \forall es. 0 \leq \{K\underscore joint}(es)$
$\{K\underscore joint\underscore nil} : \{K\underscore joint}([]) = 0$
$\{K\underscore joint\underscore singleton} : \forall e. \{K\underscore joint}([e]) = K(e)$

**compression\_axiom :**
$\forall es. (\forall e \in es. \{is\underscore presentation}(e)) \wedge es.\{length} \geq 2 \rightarrow$
$$\{K\underscore joint}(es) < \{K\underscore sum}(es)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \{is\underscore presentation}(e)) \rightarrow \{K\underscore joint}(es) \leq \{K\underscore sum}(es)$

**complexity\_positive :**
$\forall e. \{is\underscore presentation}(e) \rightarrow 0 < K(e)$

**substrate\_minimal :**
$\forall e. \{is\underscore presentation}(e) \rightarrow K(\{Substrate}) \leq K(e)$

---

### OPERATIONAL BOUNDS

$\{C\underscore nonneg} : \forall e, p. 0 \leq C(e, p)$
$\{C\underscore monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$

$\{C\underscore joint\underscore nonneg} : \forall es, p. 0 \leq \{C\underscore joint}(es, p)$

$\{K\underscore LZ\underscore nonneg} : \forall s. 0 \leq \{K\underscore LZ}(s)$
$\{K\underscore LZ\underscore empty} : \{K\underscore LZ}(\{join}([])) = 0$
$\{K\underscore LZ\underscore monotone} : \forall s_1, s_2. s_1.\{length} \leq s_2.\{length} \rightarrow \{K\underscore LZ}(s_1) \leq \{K\underscore LZ}(s_2)$

---

### TOY COMPRESSOR BOUNDS

$\{K\underscore toy\underscore lower\underscore bound} : \forall s. \{K\underscore LZ}(s) \leq \{K\underscore toy}(s)$
$\{K\underscore toy\underscore upper\underscore bound} : \forall s. \{K\underscore toy}(s) \leq \{K\underscore LZ}(s) + \log_2(s.\{length})$

---

### KLZ AXIOMS

**K\_LZ\_subadditive\_cons :**
$\forall x, xs. \{K\underscore LZ}(\{join}(x::xs)) \leq \{K\underscore LZ}(\{join}(xs)) + \{K\underscore LZ}(x) + \{c\underscore sub}$

**K\_LZ\_prefix :**
$\forall b, s. \{K\underscore LZ}(\{join}([b])) \leq \{K\underscore LZ}(\{join}(b::s))$

**K\_LZ\_singleton\_bound :**
$\forall b. \{K\underscore LZ}(\{join}([b])) \leq \{c\underscore single}$

**K\_LZ\_mode\_le :**
$\forall s. \{K\underscore LZ}(\{mode}(s)) \leq \{K\underscore LZ}(s) + \{C\underscore mode}$

**K\_LZ\_mode\_absolute\_bound :**
$\forall s. \{K\underscore LZ}(\{mode}(s)) \leq \{C\underscore mode}$

**C\_mode\_lt\_c\_grounding :**
$\{C\underscore mode} < \{c\underscore grounding}$

**K\_LZ\_cohesion\_bound\_raw :**
$\forall n, h. \{K\underscore LZ}(\{R\underscore Cohesion}(n, h)) \leq \{C\underscore coh}$

---

### TIME ARROW THEOREMS

**time\_arrow\_reduction :**
$\forall \{hist}, n.$
$$\{K\underscore LZ}(\{join}(\{mode}(\{join}(n)) :: \{hist})) \leq \{K\underscore LZ}(\{join}(\{hist})) + \{c\underscore time\underscore reduction}$$

**time\_arrow\_cohesion :**
$\forall \{hist}, n, h.$
$$\{K\underscore LZ}(\{join}(\{R\underscore Cohesion}(n, h) :: \{hist})) \leq \{K\underscore LZ}(\{join}(\{hist})) + \{c\underscore time\underscore cohesion}$$

---

### COHERENCE BOUNDS

**coherence\_bounds :**
$\forall es, \{times}.$
$$(\forall e \in es. \{is\underscore presentation}(e)) \rightarrow 0 \leq \{Coh}(es, \{times}) \wedge \{Coh}(es, \{times}) \leq 1$$

**compression\_ratio\_ge\_one :**
$\forall es, \{times}.$
$$(\forall e \in es. \{is\underscore presentation}(e)) \rightarrow 1 \leq \{compression\underscore ratio}(es, \{times})$$

---

### ERROR BOUNDS

**error\_bound\_linear :**
$\exists c > 0. \forall e, p. \{is\underscore presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p$$

**error\_bound\_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. \{is\underscore presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p^\alpha$$

**error\_bound\_general :**
$\exists M > 0. \forall e, p. \{is\underscore presentation}(e) \rightarrow$
$$|C(e, p) - K(e)| \leq M/(p+1)$$

---

### PHYSICS CORRESPONDENCES

$\{energy\underscore of}(e) = \kappa_{energy} \cdot K(e)$
$\{mass}(e) = \{energy\underscore of}(e)/c^2$
$\{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$

$\{is\underscore quantum}(\{nbhd}) := \{K\underscore LZ}(\{join}(\{nbhd})) \leq \{c\underscore grounding}$
$\{is\underscore classical}(\{nbhd}) := \{K\underscore LZ}(\{join}(\{nbhd})) > \{c\underscore grounding}$

---

### PREDICATES

$\{is\underscore substrate} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore emergent} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore temporal\underscore presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore static\underscore presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore quantum\underscore state} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore measurement\underscore device} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\underscore observable} : \{Entity} \rightarrow \{Prop}$ (axiom)

$\{phenomenal} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{has\underscore mass} : \{Entity} \rightarrow \{Prop}$ (axiom)

$\{grounds} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{temporal\underscore grounds} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity} \rightarrow \{Time} \rightarrow \{Prop}$ (axiom)
$\{interacts} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{inseparable} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{emerges\underscore from} : \{Entity} \rightarrow \{List Entity} \rightarrow \{Prop}$ (axiom)
$\{phase\underscore coupled} : \{Entity} \rightarrow \{Entity} \rightarrow \{Phase} \rightarrow \{Prop}$ (axiom)

$\{coherent} : \{Entity} \rightarrow \{Prop}$
$\{decoherent} : \{Entity} \rightarrow \{Prop}$
$\{stable} : \{Entity} \rightarrow \{Prop}$

$\{is\underscore quantum} : \{List State} \rightarrow \{Prop}$
$\{is\underscore classical} : \{List State} \rightarrow \{Prop}$
$\{coherent\underscore state} : \{KLZ.State} \rightarrow \{Prop}$

$\{is\underscore grounded} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$

---

### ENTITY CLASSIFICATION

**entity\_classification :**
$\forall e. (\{is\underscore substrate}(e) \wedge e = \{Substrate}) \vee \{is\underscore presentation}(e) \vee \{is\underscore emergent}(e)$

$\{substrate\underscore not\underscore presentation} : \forall e. \neg(\{is\underscore substrate}(e) \wedge \{is\underscore presentation}(e))$
$\{substrate\underscore not\underscore emergent} : \forall e. \neg(\{is\underscore substrate}(e) \wedge \{is\underscore emergent}(e))$
$\{presentation\underscore not\underscore emergent} : \forall e. \neg(\{is\underscore presentation}(e) \wedge \{is\underscore emergent}(e))$

**presentation\_temporal\_or\_static :**
$\forall e. \{is\underscore presentation}(e) \rightarrow$
$$(\{is\underscore temporal\underscore presentation}(e) \vee \{is\underscore static\underscore presentation}(e)) \wedge$$
$$\neg(\{is\underscore temporal\underscore presentation}(e) \wedge \{is\underscore static\underscore presentation}(e))$$

---

### SUBSTRATE PROPERTIES

$\{substrate\underscore unique} : \forall x, y. \{is\underscore substrate}(x) \wedge \{is\underscore substrate}(y) \rightarrow x = y$
$\{substrate\underscore is\underscore Substrate} : \{is\underscore substrate}(\{Substrate})$
$\{Omega\underscore is\underscore substrate} : \{is\underscore substrate}(\Omega)$
$\{Omega\underscore eq\underscore Substrate} : \Omega = \{Substrate}$

---

### TEMPORAL PRESERVATION

**indexed\_preserves\_presentation :**
$\forall e, t. \{is\underscore presentation}(e) \rightarrow \{is\underscore presentation}(\{indexed}(e, t))$

**temporal\_slice\_preserves\_presentation :**
$\forall es, t. (\forall e \in es. \{is\underscore presentation}(e)) \rightarrow$
$$(\forall e \in \{temporal\underscore slice}(es, t). \{is\underscore presentation}(e))$$

---

### ASSOCIATIVITY

**join\_associative :**
$\forall s_1, s_2, s_3. \{join}([\{join}([s_1, s_2]), s_3]) = \{join}([s_1, \{join}([s_2, s_3])])$

---

### VERIFIED THEOREMS

**energy\_from\_complexity :**
$\forall e. \{is\underscore presentation}(e) \rightarrow \{has\underscore mass}(e) \rightarrow$
$$\exists m > 0. m = \{energy\underscore of}(e)/c^2$$

**entropy\_from\_complexity :**
$\forall e. \{is\underscore presentation}(e) \rightarrow \exists S.$
$$S = k_B \cdot \log(2) \cdot K(e)$$

**coherence\_participation\_invariant :**
$\forall e. \{is\underscore temporal\underscore presentation}(e) \rightarrow \{coherent}(e) \rightarrow$
$$0 < \{P\underscore total}(e) \wedge \{Coh\underscore trajectory}(e) = 1/\{P\underscore total}(e)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \{is\underscore presentation}(e)) \rightarrow \{K\underscore joint}(es) \leq \{K\underscore sum}(es)$

**complexity\_subadditive :**
$\forall e_1, e_2. \{is\underscore presentation}(e_1) \rightarrow \{is\underscore presentation}(e_2) \rightarrow$
$$\{K\underscore joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$

**compression\_ratio\_ge\_one :**
$\forall es, \{times}. (\forall e \in es. \{is\underscore presentation}(e)) \rightarrow$
$$1 \leq \{Compression\underscore ratio}(es, \{times})$$

**R\_G1\_preserves\_grounding :**
$\forall n. \{K\underscore LZ}(\{mode}(\{join}(n))) < \{K\underscore LZ}(\{join}(n)) + \{c\underscore grounding}$

**time\_arrow\_reduction :**
$\forall \{hist}, n. \{K\underscore LZ}(\{join}(\{mode}(\{join}(n))::\{hist})) \leq \{K\underscore LZ}(\{join}(\{hist})) + \{c\underscore time\underscore reduction}$

**time\_arrow\_cohesion :**
$\forall \{hist}, n, h. \{K\underscore LZ}(\{join}(\{R\underscore Cohesion}(n, h)::\{hist})) \leq \{K\underscore LZ}(\{join}(\{hist})) + \{c\underscore time\underscore cohesion}$

**P3\_C6\_preservation :**
$\forall n, h. \{coherent\underscore state}(\{join}(n)) \rightarrow \{K\underscore LZ}(\{R\underscore G1}(n, h)) = \{K\underscore LZ}(h)$

**R\_G1\_grounding\_reduction :**
$\forall n, h. \{K\underscore LZ}(\{join}(n)) > \{c\underscore grounding} \rightarrow$
$$\{K\underscore LZ}(\{R\underscore G1}(n, h)) < \{K\underscore LZ}(\{join}(n)) + \{c\underscore grounding}$$

**R\_G1\_preserves\_time\_arrow :**
$\forall \{hist}, n, h.$
$$\{K\underscore LZ}(\{join}(\{R\underscore G1}(n, h)::\{hist})) \leq \{K\underscore LZ}(\{join}(\{Lz}(\{hist})) + \max(\{c\underscore time\underscore reduction}, \{c\underscore time\underscore cohesion})$$

**planck\_units\_positive :**
$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$

**error\_bound\_exists :**
$\forall e, p. \{is\underscore presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| \leq \epsilon.\{absolute}$