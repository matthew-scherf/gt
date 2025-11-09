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
$\{K\_ sum} : \{List Entity} \rightarrow \mathbb{R}$
$$\{K\_ sum}(es) := \sum_{e \in es} K(e)$$

$\{K\_ joint} : \{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{K\_ cond} : \{Entity} \rightarrow \{Entity} \rightarrow \mathbb{R}$
$$\{K\_ cond}(e_1,e_2) := \{K\_ joint}([e_1,e_2]) - K(e_1)$$

$C : \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{C\_ sum} : \{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{C\_ sum}(es,p) := \sum_{e \in es} C(e,p)$$

$\{C\_ joint} : \{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{C\_ cond} : \{Entity} \rightarrow \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{C\_ cond}(e_1,e_2,p) := \{C\_ joint}([e_1,e_2],p) - C(e_1,p)$$

$\{K\_ LZ} : \{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational)
$\{K\_ LZ} : \{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module)

$\{K\_ toy} : \{State} \rightarrow \mathbb{N}$
$$\{K\_ toy}(s) := |\{dedup}(s)|$$

---

### RANK FUNCTIONS

$\{rank\_ K} : \{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\{rank\_ C} : \{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom)

---

### TEMPORAL FUNCTIONS

$\{indexed} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity}$ (axiom)
$\{temporal\_ slice} : \{List Entity} \rightarrow \{Time} \rightarrow \{List Entity}$
$\{slice} : \{List} (\{Entity} \times \{Time}) \rightarrow \{Time} \rightarrow \{List Entity}$

$\{join} : \{List State} \rightarrow \{State}$ (axiom)
$\{join} : \{List KLZ.State} \rightarrow \{KLZ.State}$ (axiom, KLZ module)

$\{mode} : \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable axiom)

$\{traj} : \{Entity} \rightarrow \{List} (\{Entity} \times \{Time})$
$$\{traj}(e) := (\{List.range 1000}).\{map} (\lambda n. (\{indexed } e \{ } n, n))$$

$\{P\_ total} : \{Entity} \rightarrow \mathbb{R}$
$$\{P\_ total}(e) := 1 \{ (sum of uniform weights over trajectory)}$$

---

### COHERENCE FUNCTIONS

$\{Coh} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{Coh\_ op} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\{Coh\_ trajectory} : \{Entity} \rightarrow \mathbb{R}$
$\{dCoh\_ dt} : \{Entity} \rightarrow \{Time} \rightarrow \mathbb{R}$ (noncomputable axiom)

$\{compression\_ ratio} : \{List Entity} \rightarrow \{List Time} \rightarrow \mathbb{R}$

---

### PARTITION FUNCTIONS

$\{Z\_ ideal} : \{Finset Entity} \rightarrow \mathbb{R}$
$$\{Z\_ ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$

$\{Z\_ op} : \{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\{Z\_ op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$

---

### GROUNDING FUNCTIONS

$\{grounds} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{temporal\_ grounds} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity} \rightarrow \{Time} \rightarrow \{Prop}$ (axiom)
$\{bfs\_ depth\_ C} : \{Entity} \rightarrow \mathbb{N} \rightarrow \{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\{bfs\_ grounding\_ path} : \{Entity} \rightarrow \{Finset Entity} \rightarrow \mathbb{N} \rightarrow \{Option} (\{List Entity})$

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

$\{c\_ grounding} := 50 \{ (bits)}$
$\{c\_ margin} := 5 \{ (bits)}$

---

### KLZ CONSTANTS

$\{c\_ sub} : \mathbb{R} \{ (constant)}$
$\{c\_ single} : \mathbb{R} \{ (constant)}$
$\{C\_ mode} : \mathbb{R} \{ (constant)}$
$\{C\_ coh} : \mathbb{R} \{ (constant)}$

$\{c\_ time\_ reduction} := \{c\_ sub} + \{C\_ mode}$
$\{c\_ time\_ cohesion} := \{c\_ sub} + \{C\_ coh}$

---

### THRESHOLD PARAMETERS

$\{measured\_ inseparability\_ threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\{strong\_ compression\_ threshold} : \mathbb{R}$ ($0 < \cdot < \{measured\_ inseparability\_ threshold}$)
$\{temporal\_ coherence\_ threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\{phase\_ coupling\_ threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$)
$\{baseline\_ maximal\_ compression} : \mathbb{R}$ ($1 < \cdot$)

$\{weak\_ coupling\_ threshold} : \mathbb{R}$
$\{moderate\_ coupling\_ threshold} : \mathbb{R}$
$\{strong\_ coupling\_ threshold} : \mathbb{R}$

**Hierarchy:**
$1 < \{weak\_ coupling\_ threshold} < \{moderate\_ coupling\_ threshold} < \{strong\_ coupling\_ threshold} < \{baseline\_ maximal\_ compression}$

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
$K(\{Substrate}) = 0$
$K(\Omega) = 0$

#### G1 (Substrate Grounds All)
$\forall e. \{is\_ presentation}(e) \rightarrow \{is\_ grounded}(e, \{Substrate})$
$$\{where } \{is\_ grounded}(e, \{ctx}) := \{K\_ cond}(\{ctx}, e) < K(e) - K(\{ctx}) + \{c\_ grounding}$$

#### T7 (Time Arrow)
$\forall \{hist, next.}$
$$\{hist.length} \geq 2 \rightarrow$$
$$(\forall e \in \{hist. is\_ temporal\_ presentation}(e)) \rightarrow$$
$$\{is\_ temporal\_ presentation}(\{next}) \rightarrow$$
$$\{K\_ joint}(\{next}::\{hist}) - \{K\_ joint}(\{hist}) \leq \{K\_ joint}([\{hist.last}, \{hist.init}]) - K(\{hist.init})$$

#### T4 (Emergence/Collapse)
$\forall e_{classical}, e_{quantum}.$
$$\{is\_ presentation}(e_{classical}) \rightarrow$$
$$\{is\_ quantum\_ state}(e_{quantum}) \rightarrow$$
$$\{emergent}(e_{classical}, e_{quantum}) \rightarrow$$
$$\{is\_ measurement\_ device}(e_{classical}) \vee \{is\_ observable}(e_{classical})$$
$$\{where } \{emergent}(e_{classical}, e_{quantum}) := \{K\_ cond}(\{Substrate}, e_{classical}) < K(e_{quantum})$$

#### C6 (Coherence Preservation)
$\forall e.$
$$\{is\_ quantum\_ state}(e) \rightarrow \{coherent}(e)$$
$$\{where } \{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$
$$\{K\_ cond}(\{indexed}(e, t_1), \{indexed}(e, t_2)) = \{K\_ cond}(\{indexed}(e, t_2), \{indexed}(e, t_1))$$

---

### AXIOM CONSEQUENCES

**substrate\_ultimate\_ground :**
$\forall e. \{is\_ presentation}(e) \rightarrow \exists \{path.}$
$$\{path.head} = \{Substrate} \wedge \{path.last} = e \wedge$$
$$\forall i. i+1 < \{path.length} \rightarrow \{is\_ grounded}(\{path}[i+1], \{path}[i])$$

**decoherence\_implies\_classical :**
$\forall e. \{is\_ presentation}(e) \wedge \neg\{coherent}(e) \rightarrow$
$$\exists t_0. \forall t > t_0. \neg\{is\_ quantum\_ state}(\{indexed}(e, t))$$

**measurement\_breaks\_coherence :**
$\forall e_q, e_c.$
$$\{is\_ quantum\_ state}(e_q) \wedge \{coherent}(e_q) \wedge \{emergent}(e_c, e_q) \rightarrow \neg\{coherent}(e_c)$$

**indexed\_preserves\_presentation :**
$\forall e, t. \{is\_ presentation}(e) \rightarrow \{is\_ presentation}(\{indexed}(e, t))$

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
$\forall e, \epsilon > 0.$
$$\{is\_ presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE2 (Uniform Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \{is\_ presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE3 (Probability Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \{is\_ presentation}(e)) \wedge \{Z\_ ideal}(S) > 0 \rightarrow$
$$\exists p_0. \forall p \geq p_0. \frac{|\{Z\_ op}(S, p) - \{Z\_ ideal}(S)|}{\{Z\_ ideal}(S)} < \epsilon$$

#### BRIDGE4 (Grounding Convergence)
$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \{is\_ presentation}(e_1) \wedge \{is\_ presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. \{grounds\_ K}(e_1, e_2) \leftrightarrow \{grounds\_ C}(e_1, e_2, p)$$
**where:**
$$\{grounds\_ K}(e_1, e_2) := \{K\_ cond}(e_1, e_2) < K(e_2) - K(e_1) + \{c\_ grounding}$$
$$\{grounds\_ C}(e_1, e_2, p) := \{C\_ cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \{c\_ grounding}$$

#### BRIDGE5 (Rank Stability)
$\forall S, e.$
$$e \in S \wedge \{is\_ presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. \{rank\_ C}(e, p) = \{rank\_ K}(e)$$

#### BRIDGE6 (Temporal Continuity)
$\forall e, \{times}, \epsilon > 0. \{is\_ temporal\_ presentation}(e) \rightarrow$
$$\exists p_0. \forall p \geq p_0, t \in \{times}. |\{Coh\_ op}([e], [t], p) - \{Coh}([e], [t])| < \epsilon$$

#### BRIDGE7 (Conditional Convergence)
$\forall e_1, e_2, \epsilon > 0. \{is\_ presentation}(e_1) \wedge \{is\_ presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\{C\_ cond}(e_1, e_2, p) - \{K\_ cond}(e_1, e_2)| < \epsilon$$

#### BRIDGE7_joint (Joint Convergence)
$\forall es, \epsilon > 0. (\forall e \in es. \{is\_ presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\{C\_ joint}(es, p) - \{K\_ joint}(es)| < \epsilon$$

#### BRIDGE8 (Continuum Limit)
$\forall e, \{times}, \epsilon > 0. \{is\_ temporal\_ presentation}(e) \rightarrow$
$$\exists p_0, \delta. \delta > 0 \wedge \forall p \geq p_0, t \in \{times}.$$
$$\left| \frac{\{Coh\_ op}([e], [t+\delta], p) - \{Coh\_ op}([e], [t], p)}{\delta} - \{dCoh\_ dt}(e, t) \right| < \epsilon$$

---

### CA RULES

$F : \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable)
$\{merge} : \{KLZ.State} \rightarrow \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable)

$\{R\_ Cohesion} : \{List KLZ.State} \rightarrow \{KLZ.State} \rightarrow \{KLZ.State}$ (noncomputable axiom)
$$\{R\_ Cohesion}(n, h) := \{merge}(F(\{join}(n)), h)$$

$\{R\_ Reduction} : \{List KLZ.State} \rightarrow \{KLZ.State}$
$$\{R\_ Reduction}(n) := \{mode}(\{join}(n))$$

$\{R\_ G1} : \{List KLZ.State} \rightarrow \{KLZ.State} \rightarrow \{KLZ.State}$
$$\{R\_ G1}(n, h) := \begin{cases} \{R\_ Cohesion}(n, h) & \{if } \{K\_ LZ}(\{join}(n)) \leq \{c\_ grounding} \\ \{R\_ Reduction}(n) & \{otherwise} \end{cases}$$

$\{coherent\_ state} : \{KLZ.State} \rightarrow \{Prop}$
$$\{coherent\_ state}(s) := \{K\_ LZ}(s) \leq \{c\_ grounding}$$

---

### CA PRESERVATION THEOREMS

#### P3 (C6 Preservation)
$\forall n, h.$
$$\{coherent\_ state}(\{join}(n)) \rightarrow \{K\_ LZ}(\{R\_ G1}(n, h)) = \{K\_ LZ}(h)$$

**R\_G1\_grounding\_reduction**
$\forall n, h. \{K\_ LZ}(\{join}(n)) > \{c\_ grounding} \rightarrow$
$$\{K\_ LZ}(\{R\_ G1}(n, h)) < \{K\_ LZ}(\{join}(n)) + \{c\_ grounding}$$

**R\_G1\_preserves\_time\_arrow**
$\forall \{hist}, n, h.$
$$\{K\_ LZ}(\{join}(\{R\_ G1}(n, h)::\{hist})) \leq \{K\_ LZ}(\{join}(\{hist})) + \{c\_ time}$$
$$\{where } \{c\_ time} := \max(\{c\_ time\_ reduction}, \{c\_ time\_ cohesion})$$

---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
$\forall e.$
$$\{is\_ presentation}(e) \rightarrow$$
$$(\{has\_ mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$
$$\{energy\_ of}(e) = \kappa_{energy} \cdot K(e)$$

#### G_Ψ (Grounding Stability)
$\forall e.$
$$\{stable}(e) \leftrightarrow \{K\_ cond}(\Omega, e) > \{c\_ grounding}$$
$$\{where } \{stable}(e) := \{is\_ presentation}(e) \wedge \{K\_ cond}(\Omega, e) > \{c\_ grounding}$$

#### B_Ω (Holographic Bound)
$\forall \{region, Area.}$
$$\{is\_ presentation}(\{region}) \wedge \{Area} > 0 \rightarrow K(\{region}) \leq \frac{\{Area}}{4\ell_{Planck}^2}$$

#### Ψ_I (Coherence Invariant)
$\forall e.$
$$\{is\_ temporal\_ presentation}(e) \wedge \{coherent}(e) \rightarrow \{Coh\_ trajectory}(e) \cdot \{P\_ total}(e) = 1$$

#### U_Ω (Uncertainty Principle)
$\forall e, \Delta K, \Delta t.$
$$\{is\_ temporal\_ presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$

---

### RANK SYSTEM

$\{rank\_ K}(\Omega) = 0$
$\{grounds}(e_1, e_2) \rightarrow \{rank\_ K}(e_2) < \{rank\_ K}(e_1)$
$\forall e. \exists n. \{rank\_ K}(e) = n$

$\{rank\_ C}(e, p) = \{bfs\_ depth\_ C}(e, p, S) \{ for } e \in S$

---

### UNIVERSAL GROUNDING

$\forall e. \{is\_ presentation}(e) \rightarrow \exists \{path.}$
$$\{path.head} = \Omega \wedge \{path.last} = e \wedge$$
$$\forall i. i+1 < \{path.length} \rightarrow \{grounds}(\{path}[i], \{path}[i+1])$$

**grounding\_transitive :**
$\forall e_1, e_2, e_3.$
$$\{grounds}(e_1, e_2) \wedge \{grounds}(e_2, e_3) \rightarrow \{grounds}(e_1, e_3)$$

**grounding\_acyclic :**
$\forall e. \neg\{grounds}(e, e)$

---

### COMPLEXITY BOUNDS

$\{K\_ joint\_ nonneg} : \forall es. 0 \leq \{K\_ joint}(es)$
$\{K\_ joint\_ nil} : \{K\_ joint}([]) = 0$
$\{K\_ joint\_ singleton} : \forall e. \{K\_ joint}([e]) = K(e)$

**compression\_axiom :**
$\forall es. (\forall e \in es. \{is\_ presentation}(e)) \wedge es.\{length} \geq 2 \rightarrow$
$$\{K\_ joint}(es) < \{K\_ sum}(es)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \{is\_ presentation}(e)) \rightarrow \{K\_ joint}(es) \leq \{K\_ sum}(es)$

**complexity\_positive :**
$\forall e. \{is\_ presentation}(e) \rightarrow 0 < K(e)$

**substrate\_minimal :**
$\forall e. \{is\_ presentation}(e) \rightarrow K(\{Substrate}) \leq K(e)$

---

### OPERATIONAL BOUNDS

$\{C\_ nonneg} : \forall e, p. 0 \leq C(e, p)$
$\{C\_ monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$

$\{C\_ joint\_ nonneg} : \forall es, p. 0 \leq \{C\_ joint}(es, p)$

$\{K\_ LZ\_ nonneg} : \forall s. 0 \leq \{K\_ LZ}(s)$
$\{K\_ LZ\_ empty} : \{K\_ LZ}(\{join}([])) = 0$
$\{K\_ LZ\_ monotone} : \forall s_1, s_2. s_1.\{length} \leq s_2.\{length} \rightarrow \{K\_ LZ}(s_1) \leq \{K\_ LZ}(s_2)$

---

### TOY COMPRESSOR BOUNDS

$\{K\_ toy\_ lower\_ bound} : \forall s. \{K\_ LZ}(s) \leq \{K\_ toy}(s)$
$\{K\_ toy\_ upper\_ bound} : \forall s. \{K\_ toy}(s) \leq \{K\_ LZ}(s) + \log_2(s.\{length})$

---

### KLZ AXIOMS

**K\_LZ\_subadditive\_cons :**
$\forall x, xs. \{K\_ LZ}(\{join}(x::xs)) \leq \{K\_ LZ}(\{join}(xs)) + \{K\_ LZ}(x) + \{c\_ sub}$

**K\_LZ\_prefix :**
$\forall b, s. \{K\_ LZ}(\{join}([b])) \leq \{K\_ LZ}(\{join}(b::s))$

**K\_LZ\_singleton\_bound :**
$\forall b. \{K\_ LZ}(\{join}([b])) \leq \{c\_ single}$

**K\_LZ\_mode\_le :**
$\forall s. \{K\_ LZ}(\{mode}(s)) \leq \{K\_ LZ}(s) + \{C\_ mode}$

**K\_LZ\_mode\_absolute\_bound :**
$\forall s. \{K\_ LZ}(\{mode}(s)) \leq \{C\_ mode}$

**C\_mode\_lt\_c\_grounding :**
$\{C\_ mode} < \{c\_ grounding}$

**K\_LZ\_cohesion\_bound\_raw :**
$\forall n, h. \{K\_ LZ}(\{R\_ Cohesion}(n, h)) \leq \{C\_ coh}$

---

### TIME ARROW THEOREMS

**time\_arrow\_reduction :**
$\forall \{hist}, n.$
$$\{K\_ LZ}(\{join}(\{mode}(\{join}(n)) :: \{hist})) \leq \{K\_ LZ}(\{join}(\{hist})) + \{c\_ time\_ reduction}$$

**time\_arrow\_cohesion :**
$\forall \{hist}, n, h.$
$$\{K\_ LZ}(\{join}(\{R\_ Cohesion}(n, h) :: \{hist})) \leq \{K\_ LZ}(\{join}(\{hist})) + \{c\_ time\_ cohesion}$$

---

### COHERENCE BOUNDS

**coherence\_bounds :**
$\forall es, \{times}.$
$$(\forall e \in es. \{is\_ presentation}(e)) \rightarrow 0 \leq \{Coh}(es, \{times}) \wedge \{Coh}(es, \{times}) \leq 1$$

**compression\_ratio\_ge\_one :**
$\forall es, \{times}.$
$$(\forall e \in es. \{is\_ presentation}(e)) \rightarrow 1 \leq \{compression\_ ratio}(es, \{times})$$

---

### ERROR BOUNDS

**error\_bound\_linear :**
$\exists c > 0. \forall e, p. \{is\_ presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p$$

**error\_bound\_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. \{is\_ presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p^\alpha$$

**error\_bound\_general :**
$\exists M > 0. \forall e, p. \{is\_ presentation}(e) \rightarrow$
$$|C(e, p) - K(e)| \leq M/(p+1)$$

---

### PHYSICS CORRESPONDENCES

$\{energy\_ of}(e) = \kappa_{energy} \cdot K(e)$
$\{mass}(e) = \{energy\_ of}(e)/c^2$
$\{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$

$\{is\_ quantum}(\{nbhd}) := \{K\_ LZ}(\{join}(\{nbhd})) \leq \{c\_ grounding}$
$\{is\_ classical}(\{nbhd}) := \{K\_ LZ}(\{join}(\{nbhd})) > \{c\_ grounding}$

---

### PREDICATES

$\{is\_ substrate} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ emergent} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ temporal\_ presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ static\_ presentation} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ quantum\_ state} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ measurement\_ device} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{is\_ observable} : \{Entity} \rightarrow \{Prop}$ (axiom)

$\{phenomenal} : \{Entity} \rightarrow \{Prop}$ (axiom)
$\{has\_ mass} : \{Entity} \rightarrow \{Prop}$ (axiom)

$\{grounds} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{temporal\_ grounds} : \{Entity} \rightarrow \{Time} \rightarrow \{Entity} \rightarrow \{Time} \rightarrow \{Prop}$ (axiom)
$\{interacts} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{inseparable} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$ (axiom)
$\{emerges\_ from} : \{Entity} \rightarrow \{List Entity} \rightarrow \{Prop}$ (axiom)
$\{phase\_ coupled} : \{Entity} \rightarrow \{Entity} \rightarrow \{Phase} \rightarrow \{Prop}$ (axiom)

$\{coherent} : \{Entity} \rightarrow \{Prop}$
$\{decoherent} : \{Entity} \rightarrow \{Prop}$
$\{stable} : \{Entity} \rightarrow \{Prop}$

$\{is\_ quantum} : \{List State} \rightarrow \{Prop}$
$\{is\_ classical} : \{List State} \rightarrow \{Prop}$
$\{coherent\_ state} : \{KLZ.State} \rightarrow \{Prop}$

$\{is\_ grounded} : \{Entity} \rightarrow \{Entity} \rightarrow \{Prop}$

---

### ENTITY CLASSIFICATION

**entity\_classification :**
$\forall e. (\{is\_ substrate}(e) \wedge e = \{Substrate}) \vee \{is\_ presentation}(e) \vee \{is\_ emergent}(e)$

$\{substrate\_ not\_ presentation} : \forall e. \neg(\{is\_ substrate}(e) \wedge \{is\_ presentation}(e))$
$\{substrate\_ not\_ emergent} : \forall e. \neg(\{is\_ substrate}(e) \wedge \{is\_ emergent}(e))$
$\{presentation\_ not\_ emergent} : \forall e. \neg(\{is\_ presentation}(e) \wedge \{is\_ emergent}(e))$

**presentation\_temporal\_or\_static :**
$\forall e. \{is\_ presentation}(e) \rightarrow$
$$(\{is\_ temporal\_ presentation}(e) \vee \{is\_ static\_ presentation}(e)) \wedge$$
$$\neg(\{is\_ temporal\_ presentation}(e) \wedge \{is\_ static\_ presentation}(e))$$

---

### SUBSTRATE PROPERTIES

$\{substrate\_ unique} : \forall x, y. \{is\_ substrate}(x) \wedge \{is\_ substrate}(y) \rightarrow x = y$
$\{substrate\_ is\_ Substrate} : \{is\_ substrate}(\{Substrate})$
$\{Omega\_ is\_ substrate} : \{is\_ substrate}(\Omega)$
$\{Omega\_ eq\_ Substrate} : \Omega = \{Substrate}$

---

### TEMPORAL PRESERVATION

**indexed\_preserves\_presentation :**
$\forall e, t. \{is\_ presentation}(e) \rightarrow \{is\_ presentation}(\{indexed}(e, t))$

**temporal\_slice\_preserves\_presentation :**
$\forall es, t. (\forall e \in es. \{is\_ presentation}(e)) \rightarrow$
$$(\forall e \in \{temporal\_ slice}(es, t). \{is\_ presentation}(e))$$

---

### ASSOCIATIVITY

**join\_associative :**
$\forall s_1, s_2, s_3. \{join}([\{join}([s_1, s_2]), s_3]) = \{join}([s_1, \{join}([s_2, s_3])])$

---

### VERIFIED THEOREMS

**energy\_from\_complexity :**
$\forall e. \{is\_ presentation}(e) \rightarrow \{has\_ mass}(e) \rightarrow$
$$\exists m > 0. m = \{energy\_ of}(e)/c^2$$

**entropy\_from\_complexity :**
$\forall e. \{is\_ presentation}(e) \rightarrow \exists S.$
$$S = k_B \cdot \log(2) \cdot K(e)$$

**coherence\_participation\_invariant :**
$\forall e. \{is\_ temporal\_ presentation}(e) \rightarrow \{coherent}(e) \rightarrow$
$$0 < \{P\_ total}(e) \wedge \{Coh\_ trajectory}(e) = 1/\{P\_ total}(e)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \{is\_ presentation}(e)) \rightarrow \{K\_ joint}(es) \leq \{K\_ sum}(es)$

**complexity\_subadditive :**
$\forall e_1, e_2. \{is\_ presentation}(e_1) \rightarrow \{is\_ presentation}(e_2) \rightarrow$
$$\{K\_ joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$

**compression\_ratio\_ge\_one :**
$\forall es, \{times}. (\forall e \in es. \{is\_ presentation}(e)) \rightarrow$
$$1 \leq \{Compression\_ ratio}(es, \{times})$$

**R\_G1\_preserves\_grounding :**
$\forall n. \{K\_ LZ}(\{mode}(\{join}(n))) < \{K\_ LZ}(\{join}(n)) + \{c\_ grounding}$

**time\_arrow\_reduction :**
$\forall \{hist}, n. \{K\_ LZ}(\{join}(\{mode}(\{join}(n))::\{hist})) \leq \{K\_ LZ}(\{join}(\{hist})) + \{c\_ time\_ reduction}$

**time\_arrow\_cohesion :**
$\forall \{hist}, n, h. \{K\_ LZ}(\{join}(\{R\_ Cohesion}(n, h)::\{hist})) \leq \{K\_ LZ}(\{join}(\{hist})) + \{c\_ time\_ cohesion}$

**P3\_C6\_preservation :**
$\forall n, h. \{coherent\_ state}(\{join}(n)) \rightarrow \{K\_ LZ}(\{R\_ G1}(n, h)) = \{K\_ LZ}(h)$

**R\_G1\_grounding\_reduction :**
$\forall n, h. \{K\_ LZ}(\{join}(n)) > \{c\_ grounding} \rightarrow$
$$\{K\_ LZ}(\{R\_ G1}(n, h)) < \{K\_ LZ}(\{join}(n)) + \{c\_ grounding}$$

**R\_G1\_preserves\_time\_arrow :**
$\forall \{hist}, n, h.$
$$\{K\_ LZ}(\{join}(\{R\_ G1}(n, h)::\{hist})) \leq \{K\_ LZ}(\{join}(\{Lz}(\{hist})) + \max(\{c\_ time\_ reduction}, \{c\_ time\_ cohesion})$$

**planck\_units\_positive :**
$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$

**error\_bound\_exists :**
$\forall e, p. \{is\_ presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| \leq \epsilon.\{absolute}$