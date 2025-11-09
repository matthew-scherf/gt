## SUBSTRATE THEORY — FORMAL SPECIFICATION (LEAN 4 VERIFIED)
Matthew Scherf 2025

---

### TYPES

$\\_{State} := \\_{List Bool}$
$\\_{Entity} : \\_{opaque type}$
$\Omega : \\_{Entity}$ (axiom)
$\\_{Substrate} : \\_{Entity}$ (axiom)
$\\_{Time} := \mathbb{R}$
$\\_{Phase} := \mathbb{R}$
$\\_{Nbhd} := \\_{List State}$
$\\_{Precision} := \mathbb{N}$

$\\_{KLZ.State} : \\_{Type}$ (axiom)

---

### COMPLEXITY FUNCTIONS

$K : \\_{Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\\_{K\_ sum} : \\_{List Entity} \rightarrow \mathbb{R}$
$$\\_{K\_ sum}(es) := \sum_{e \in es} K(e)$$

$\\_{K\_ joint} : \\_{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\\_{K\_ cond} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \mathbb{R}$
$$\\_{K\_ cond}(e_1,e_2) := \\_{K\_ joint}([e_1,e_2]) - K(e_1)$$

$C : \\_{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\\_{C\_ sum} : \\_{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\\_{C\_ sum}(es,p) := \sum_{e \in es} C(e,p)$$

$\\_{C\_ joint} : \\_{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\\_{C\_ cond} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\\_{C\_ cond}(e_1,e_2,p) := \\_{C\_ joint}([e_1,e_2],p) - C(e_1,p)$$

$\\_{K\_ LZ} : \\_{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational)
$\\_{K\_ LZ} : \\_{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module)

$\\_{K\_ toy} : \\_{State} \rightarrow \mathbb{N}$
$$\\_{K\_ toy}(s) := |\\_{dedup}(s)|$$

---

### RANK FUNCTIONS

$\\_{rank\_ K} : \\_{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\\_{rank\_ C} : \\_{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom)

---

### TEMPORAL FUNCTIONS

$\\_{indexed} : \\_{Entity} \rightarrow \\_{Time} \rightarrow \\_{Entity}$ (axiom)
$\\_{temporal\_ slice} : \\_{List Entity} \rightarrow \\_{Time} \rightarrow \\_{List Entity}$
$\\_{slice} : \\_{List} (\\_{Entity} \times \\_{Time}) \rightarrow \\_{Time} \rightarrow \\_{List Entity}$

$\\_{join} : \\_{List State} \rightarrow \\_{State}$ (axiom)
$\\_{join} : \\_{List KLZ.State} \rightarrow \\_{KLZ.State}$ (axiom, KLZ module)

$\\_{mode} : \\_{KLZ.State} \rightarrow \\_{KLZ.State}$ (noncomputable axiom)

$\\_{traj} : \\_{Entity} \rightarrow \\_{List} (\\_{Entity} \times \\_{Time})$
$$\\_{traj}(e) := (\\_{List.range 1000}).\\_{map} (\lambda n. (\\_{indexed } e \\_{ } n, n))$$

$\\_{P\_ total} : \\_{Entity} \rightarrow \mathbb{R}$
$$\\_{P\_ total}(e) := 1 \\_{ (sum of uniform weights over trajectory)}$$

---

### COHERENCE FUNCTIONS

$\\_{Coh} : \\_{List Entity} \rightarrow \\_{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\\_{Coh\_ op} : \\_{List Entity} \rightarrow \\_{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\\_{Coh\_ trajectory} : \\_{Entity} \rightarrow \mathbb{R}$
$\\_{dCoh\_ dt} : \\_{Entity} \rightarrow \\_{Time} \rightarrow \mathbb{R}$ (noncomputable axiom)

$\\_{compression\_ ratio} : \\_{List Entity} \rightarrow \\_{List Time} \rightarrow \mathbb{R}$

---

### PARTITION FUNCTIONS

$\\_{Z\_ ideal} : \\_{Finset Entity} \rightarrow \mathbb{R}$
$$\\_{Z\_ ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$

$\\_{Z\_ op} : \\_{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\\_{Z\_ op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$

---

### GROUNDING FUNCTIONS

$\\_{grounds} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{temporal\_ grounds} : \\_{Entity} \rightarrow \\_{Time} \rightarrow \\_{Entity} \rightarrow \\_{Time} \rightarrow \\_{Prop}$ (axiom)
$\\_{bfs\_ depth\_ C} : \\_{Entity} \rightarrow \mathbb{N} \rightarrow \\_{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\\_{bfs\_ grounding\_ path} : \\_{Entity} \rightarrow \\_{Finset Entity} \rightarrow \mathbb{N} \rightarrow \\_{Option} (\\_{List Entity})$

---

### PHYSICAL CONSTANTS

$c := 299792458 \\_{ m/s}$
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
$t_{universe} : \mathbb{R}$ ($13.7 \times 10^9 < t_{universe} < 13.9 \times 10^9 \\_{ years}$)

$N_e : \mathbb{R}$ ($50 < N_e < 70$, e-folds of inflation)
$n_s : \mathbb{R}$ ($0.96 < n_s < 0.97$, scalar spectral index)
$r_s : \mathbb{R}$ ($0 \leq r_s < 0.036$, tensor-to-scalar ratio)
$z_{transition} : \mathbb{R}$ ($0.6 < z_{transition} < 0.8$, matter-$\Lambda$ transition)

---

### GROUNDING CONSTANTS

$\\_{c\_ grounding} := 50 \\_{ (bits)}$
$\\_{c\_ margin} := 5 \\_{ (bits)}$

---

### KLZ CONSTANTS

$\\_{c\_ sub} : \mathbb{R} \\_{ (constant)}$
$\\_{c\_ single} : \mathbb{R} \\_{ (constant)}$
$\\_{C\_ mode} : \mathbb{R} \\_{ (constant)}$
$\\_{C\_ coh} : \mathbb{R} \\_{ (constant)}$

$\\_{c\_ time\_ reduction} := \\_{c\_ sub} + \\_{C\_ mode}$
$\\_{c\_ time\_ cohesion} := \\_{c\_ sub} + \\_{C\_ coh}$

---

### THRESHOLD PARAMETERS

$\\_{measured\_ inseparability\_ threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\\_{strong\_ compression\_ threshold} : \mathbb{R}$ ($0 < \cdot < \\_{measured\_ inseparability\_ threshold}$)
$\\_{temporal\_ coherence\_ threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\\_{phase\_ coupling\_ threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$)
$\\_{baseline\_ maximal\_ compression} : \mathbb{R}$ ($1 < \cdot$)

$\\_{weak\_ coupling\_ threshold} : \mathbb{R}$
$\\_{moderate\_ coupling\_ threshold} : \mathbb{R}$
$\\_{strong\_ coupling\_ threshold} : \mathbb{R}$

**Hierarchy:**
$1 < \\_{weak\_ coupling\_ threshold} < \\_{moderate\_ coupling\_ threshold} < \\_{strong\_ coupling\_ threshold} < \\_{baseline\_ maximal\_ compression}$

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
$K(\\_{Substrate}) = 0$
$K(\Omega) = 0$

#### G1 (Substrate Grounds All)
$\forall e. \\_{is\_ presentation}(e) \rightarrow \\_{is\_ grounded}(e, \\_{Substrate})$
$$\\_{where } \\_{is\_ grounded}(e, \\_{ctx}) := \\_{K\_ cond}(\\_{ctx}, e) < K(e) - K(\\_{ctx}) + \\_{c\_ grounding}$$

#### T7 (Time Arrow)
$\forall \\_{hist, next.}$
$$\\_{hist.length} \geq 2 \rightarrow$$
$$(\forall e \in \\_{hist. is\_ temporal\_ presentation}(e)) \rightarrow$$
$$\\_{is\_ temporal\_ presentation}(\\_{next}) \rightarrow$$
$$\\_{K\_ joint}(\\_{next}::\\_{hist}) - \\_{K\_ joint}(\\_{hist}) \leq \\_{K\_ joint}([\\_{hist.last}, \\_{hist.init}]) - K(\\_{hist.init})$$

#### T4 (Emergence/Collapse)
$\forall e_{classical}, e_{quantum}.$
$$\\_{is\_ presentation}(e_{classical}) \rightarrow$$
$$\\_{is\_ quantum\_ state}(e_{quantum}) \rightarrow$$
$$\\_{emergent}(e_{classical}, e_{quantum}) \rightarrow$$
$$\\_{is\_ measurement\_ device}(e_{classical}) \vee \\_{is\_ observable}(e_{classical})$$
$$\\_{where } \\_{emergent}(e_{classical}, e_{quantum}) := \\_{K\_ cond}(\\_{Substrate}, e_{classical}) < K(e_{quantum})$$

#### C6 (Coherence Preservation)
$\forall e.$
$$\\_{is\_ quantum\_ state}(e) \rightarrow \\_{coherent}(e)$$
$$\\_{where } \\_{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$
$$\\_{K\_ cond}(\\_{indexed}(e, t_1), \\_{indexed}(e, t_2)) = \\_{K\_ cond}(\\_{indexed}(e, t_2), \\_{indexed}(e, t_1))$$

---

### AXIOM CONSEQUENCES

**substrate\_ultimate\_ground :**
$\forall e. \\_{is\_ presentation}(e) \rightarrow \exists \\_{path.}$
$$\\_{path.head} = \\_{Substrate} \wedge \\_{path.last} = e \wedge$$
$$\forall i. i+1 < \\_{path.length} \rightarrow \\_{is\_ grounded}(\\_{path}[i+1], \\_{path}[i])$$

**decoherence\_implies\_classical :**
$\forall e. \\_{is\_ presentation}(e) \wedge \neg\\_{coherent}(e) \rightarrow$
$$\exists t_0. \forall t > t_0. \neg\\_{is\_ quantum\_ state}(\\_{indexed}(e, t))$$

**measurement\_breaks\_coherence :**
$\forall e_q, e_c.$
$$\\_{is\_ quantum\_ state}(e_q) \wedge \\_{coherent}(e_q) \wedge \\_{emergent}(e_c, e_q) \rightarrow \neg\\_{coherent}(e_c)$$

**indexed\_preserves\_presentation :**
$\forall e, t. \\_{is\_ presentation}(e) \rightarrow \\_{is\_ presentation}(\\_{indexed}(e, t))$

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
$\forall e, \epsilon > 0.$
$$\\_{is\_ presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE2 (Uniform Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \\_{is\_ presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE3 (Probability Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \\_{is\_ presentation}(e)) \wedge \\_{Z\_ ideal}(S) > 0 \rightarrow$
$$\exists p_0. \forall p \geq p_0. \frac{|\\_{Z\_ op}(S, p) - \\_{Z\_ ideal}(S)|}{\\_{Z\_ ideal}(S)} < \epsilon$$

#### BRIDGE4 (Grounding Convergence)
$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \\_{is\_ presentation}(e_1) \wedge \\_{is\_ presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. \\_{grounds\_ K}(e_1, e_2) \leftrightarrow \\_{grounds\_ C}(e_1, e_2, p)$$
**where:**
$$\\_{grounds\_ K}(e_1, e_2) := \\_{K\_ cond}(e_1, e_2) < K(e_2) - K(e_1) + \\_{c\_ grounding}$$
$$\\_{grounds\_ C}(e_1, e_2, p) := \\_{C\_ cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \\_{c\_ grounding}$$

#### BRIDGE5 (Rank Stability)
$\forall S, e.$
$$e \in S \wedge \\_{is\_ presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. \\_{rank\_ C}(e, p) = \\_{rank\_ K}(e)$$

#### BRIDGE6 (Temporal Continuity)
$\forall e, \\_{times}, \epsilon > 0. \\_{is\_ temporal\_ presentation}(e) \rightarrow$
$$\exists p_0. \forall p \geq p_0, t \in \\_{times}. |\\_{Coh\_ op}([e], [t], p) - \\_{Coh}([e], [t])| < \epsilon$$

#### BRIDGE7 (Conditional Convergence)
$\forall e_1, e_2, \epsilon > 0. \\_{is\_ presentation}(e_1) \wedge \\_{is\_ presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\\_{C\_ cond}(e_1, e_2, p) - \\_{K\_ cond}(e_1, e_2)| < \epsilon$$

#### BRIDGE7_joint (Joint Convergence)
$\forall es, \epsilon > 0. (\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\\_{C\_ joint}(es, p) - \\_{K\_ joint}(es)| < \epsilon$$

#### BRIDGE8 (Continuum Limit)
$\forall e, \\_{times}, \epsilon > 0. \\_{is\_ temporal\_ presentation}(e) \rightarrow$
$$\exists p_0, \delta. \delta > 0 \wedge \forall p \geq p_0, t \in \\_{times}.$$
$$\left| \frac{\\_{Coh\_ op}([e], [t+\delta], p) - \\_{Coh\_ op}([e], [t], p)}{\delta} - \\_{dCoh\_ dt}(e, t) \right| < \epsilon$$

---

### CA RULES

$F : \\_{KLZ.State} \rightarrow \\_{KLZ.State}$ (noncomputable)
$\\_{merge} : \\_{KLZ.State} \rightarrow \\_{KLZ.State} \rightarrow \\_{KLZ.State}$ (noncomputable)

$\\_{R\_ Cohesion} : \\_{List KLZ.State} \rightarrow \\_{KLZ.State} \rightarrow \\_{KLZ.State}$ (noncomputable axiom)
$$\\_{R\_ Cohesion}(n, h) := \\_{merge}(F(\\_{join}(n)), h)$$

$\\_{R\_ Reduction} : \\_{List KLZ.State} \rightarrow \\_{KLZ.State}$
$$\\_{R\_ Reduction}(n) := \\_{mode}(\\_{join}(n))$$

$\\_{R\_ G1} : \\_{List KLZ.State} \rightarrow \\_{KLZ.State} \rightarrow \\_{KLZ.State}$
$$\\_{R\_ G1}(n, h) := \begin{cases} \\_{R\_ Cohesion}(n, h) & \\_{if } \\_{K\_ LZ}(\\_{join}(n)) \leq \\_{c\_ grounding} \\ \\_{R\_ Reduction}(n) & \\_{otherwise} \end{cases}$$

$\\_{coherent\_ state} : \\_{KLZ.State} \rightarrow \\_{Prop}$
$$\\_{coherent\_ state}(s) := \\_{K\_ LZ}(s) \leq \\_{c\_ grounding}$$

---

### CA PRESERVATION THEOREMS

#### P3 (C6 Preservation)
$\forall n, h.$
$$\\_{coherent\_ state}(\\_{join}(n)) \rightarrow \\_{K\_ LZ}(\\_{R\_ G1}(n, h)) = \\_{K\_ LZ}(h)$$

**R\_G1\_grounding\_reduction**
$\forall n, h. \\_{K\_ LZ}(\\_{join}(n)) > \\_{c\_ grounding} \rightarrow$
$$\\_{K\_ LZ}(\\_{R\_ G1}(n, h)) < \\_{K\_ LZ}(\\_{join}(n)) + \\_{c\_ grounding}$$

**R\_G1\_preserves\_time\_arrow**
$\forall \\_{hist}, n, h.$
$$\\_{K\_ LZ}(\\_{join}(\\_{R\_ G1}(n, h)::\\_{hist})) \leq \\_{K\_ LZ}(\\_{join}(\\_{hist})) + \\_{c\_ time}$$
$$\\_{where } \\_{c\_ time} := \max(\\_{c\_ time\_ reduction}, \\_{c\_ time\_ cohesion})$$

---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
$\forall e.$
$$\\_{is\_ presentation}(e) \rightarrow$$
$$(\\_{has\_ mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$
$$\\_{energy\_ of}(e) = \kappa_{energy} \cdot K(e)$$

#### G_Ψ (Grounding Stability)
$\forall e.$
$$\\_{stable}(e) \leftrightarrow \\_{K\_ cond}(\Omega, e) > \\_{c\_ grounding}$$
$$\\_{where } \\_{stable}(e) := \\_{is\_ presentation}(e) \wedge \\_{K\_ cond}(\Omega, e) > \\_{c\_ grounding}$$

#### B_Ω (Holographic Bound)
$\forall \\_{region, Area.}$
$$\\_{is\_ presentation}(\\_{region}) \wedge \\_{Area} > 0 \rightarrow K(\\_{region}) \leq \frac{\\_{Area}}{4\ell_{Planck}^2}$$

#### Ψ_I (Coherence Invariant)
$\forall e.$
$$\\_{is\_ temporal\_ presentation}(e) \wedge \\_{coherent}(e) \rightarrow \\_{Coh\_ trajectory}(e) \cdot \\_{P\_ total}(e) = 1$$

#### U_Ω (Uncertainty Principle)
$\forall e, \Delta K, \Delta t.$
$$\\_{is\_ temporal\_ presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$

---

### RANK SYSTEM

$\\_{rank\_ K}(\Omega) = 0$
$\\_{grounds}(e_1, e_2) \rightarrow \\_{rank\_ K}(e_2) < \\_{rank\_ K}(e_1)$
$\forall e. \exists n. \\_{rank\_ K}(e) = n$

$\\_{rank\_ C}(e, p) = \\_{bfs\_ depth\_ C}(e, p, S) \\_{ for } e \in S$

---

### UNIVERSAL GROUNDING

$\forall e. \\_{is\_ presentation}(e) \rightarrow \exists \\_{path.}$
$$\\_{path.head} = \Omega \wedge \\_{path.last} = e \wedge$$
$$\forall i. i+1 < \\_{path.length} \rightarrow \\_{grounds}(\\_{path}[i], \\_{path}[i+1])$$

**grounding\_transitive :**
$\forall e_1, e_2, e_3.$
$$\\_{grounds}(e_1, e_2) \wedge \\_{grounds}(e_2, e_3) \rightarrow \\_{grounds}(e_1, e_3)$$

**grounding\_acyclic :**
$\forall e. \neg\\_{grounds}(e, e)$

---

### COMPLEXITY BOUNDS

$\\_{K\_ joint\_ nonneg} : \forall es. 0 \leq \\_{K\_ joint}(es)$
$\\_{K\_ joint\_ nil} : \\_{K\_ joint}([]) = 0$
$\\_{K\_ joint\_ singleton} : \forall e. \\_{K\_ joint}([e]) = K(e)$

**compression\_axiom :**
$\forall es. (\forall e \in es. \\_{is\_ presentation}(e)) \wedge es.\\_{length} \geq 2 \rightarrow$
$$\\_{K\_ joint}(es) < \\_{K\_ sum}(es)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow \\_{K\_ joint}(es) \leq \\_{K\_ sum}(es)$

**complexity\_positive :**
$\forall e. \\_{is\_ presentation}(e) \rightarrow 0 < K(e)$

**substrate\_minimal :**
$\forall e. \\_{is\_ presentation}(e) \rightarrow K(\\_{Substrate}) \leq K(e)$

---

### OPERATIONAL BOUNDS

$\\_{C\_ nonneg} : \forall e, p. 0 \leq C(e, p)$
$\\_{C\_ monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$

$\\_{C\_ joint\_ nonneg} : \forall es, p. 0 \leq \\_{C\_ joint}(es, p)$

$\\_{K\_ LZ\_ nonneg} : \forall s. 0 \leq \\_{K\_ LZ}(s)$
$\\_{K\_ LZ\_ empty} : \\_{K\_ LZ}(\\_{join}([])) = 0$
$\\_{K\_ LZ\_ monotone} : \forall s_1, s_2. s_1.\\_{length} \leq s_2.\\_{length} \rightarrow \\_{K\_ LZ}(s_1) \leq \\_{K\_ LZ}(s_2)$

---

### TOY COMPRESSOR BOUNDS

$\\_{K\_ toy\_ lower\_ bound} : \forall s. \\_{K\_ LZ}(s) \leq \\_{K\_ toy}(s)$
$\\_{K\_ toy\_ upper\_ bound} : \forall s. \\_{K\_ toy}(s) \leq \\_{K\_ LZ}(s) + \log_2(s.\\_{length})$

---

### KLZ AXIOMS

**K\_LZ\_subadditive\_cons :**
$\forall x, xs. \\_{K\_ LZ}(\\_{join}(x::xs)) \leq \\_{K\_ LZ}(\\_{join}(xs)) + \\_{K\_ LZ}(x) + \\_{c\_ sub}$

**K\_LZ\_prefix :**
$\forall b, s. \\_{K\_ LZ}(\\_{join}([b])) \leq \\_{K\_ LZ}(\\_{join}(b::s))$

**K\_LZ\_singleton\_bound :**
$\forall b. \\_{K\_ LZ}(\\_{join}([b])) \leq \\_{c\_ single}$

**K\_LZ\_mode\_le :**
$\forall s. \\_{K\_ LZ}(\\_{mode}(s)) \leq \\_{K\_ LZ}(s) + \\_{C\_ mode}$

**K\_LZ\_mode\_absolute\_bound :**
$\forall s. \\_{K\_ LZ}(\\_{mode}(s)) \leq \\_{C\_ mode}$

**C\_mode\_lt\_c\_grounding :**
$\\_{C\_ mode} < \\_{c\_ grounding}$

**K\_LZ\_cohesion\_bound\_raw :**
$\forall n, h. \\_{K\_ LZ}(\\_{R\_ Cohesion}(n, h)) \leq \\_{C\_ coh}$

---

### TIME ARROW THEOREMS

**time\_arrow\_reduction :**
$\forall \\_{hist}, n.$
$$\\_{K\_ LZ}(\\_{join}(\\_{mode}(\\_{join}(n)) :: \\_{hist})) \leq \\_{K\_ LZ}(\\_{join}(\\_{hist})) + \\_{c\_ time\_ reduction}$$

**time\_arrow\_cohesion :**
$\forall \\_{hist}, n, h.$
$$\\_{K\_ LZ}(\\_{join}(\\_{R\_ Cohesion}(n, h) :: \\_{hist})) \leq \\_{K\_ LZ}(\\_{join}(\\_{hist})) + \\_{c\_ time\_ cohesion}$$

---

### COHERENCE BOUNDS

**coherence\_bounds :**
$\forall es, \\_{times}.$
$$(\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow 0 \leq \\_{Coh}(es, \\_{times}) \wedge \\_{Coh}(es, \\_{times}) \leq 1$$

**compression\_ratio\_ge\_one :**
$\forall es, \\_{times}.$
$$(\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow 1 \leq \\_{compression\_ ratio}(es, \\_{times})$$

---

### ERROR BOUNDS

**error\_bound\_linear :**
$\exists c > 0. \forall e, p. \\_{is\_ presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p$$

**error\_bound\_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. \\_{is\_ presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p^\alpha$$

**error\_bound\_general :**
$\exists M > 0. \forall e, p. \\_{is\_ presentation}(e) \rightarrow$
$$|C(e, p) - K(e)| \leq M/(p+1)$$

---

### PHYSICS CORRESPONDENCES

$\\_{energy\_ of}(e) = \kappa_{energy} \cdot K(e)$
$\\_{mass}(e) = \\_{energy\_ of}(e)/c^2$
$\\_{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$

$\\_{is\_ quantum}(\\_{nbhd}) := \\_{K\_ LZ}(\\_{join}(\\_{nbhd})) \leq \\_{c\_ grounding}$
$\\_{is\_ classical}(\\_{nbhd}) := \\_{K\_ LZ}(\\_{join}(\\_{nbhd})) > \\_{c\_ grounding}$

---

### PREDICATES

$\\_{is\_ substrate} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ presentation} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ emergent} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ temporal\_ presentation} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ static\_ presentation} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ quantum\_ state} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ measurement\_ device} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{is\_ observable} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)

$\\_{phenomenal} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{has\_ mass} : \\_{Entity} \rightarrow \\_{Prop}$ (axiom)

$\\_{grounds} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{temporal\_ grounds} : \\_{Entity} \rightarrow \\_{Time} \rightarrow \\_{Entity} \rightarrow \\_{Time} \rightarrow \\_{Prop}$ (axiom)
$\\_{interacts} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{inseparable} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{emerges\_ from} : \\_{Entity} \rightarrow \\_{List Entity} \rightarrow \\_{Prop}$ (axiom)
$\\_{phase\_ coupled} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \\_{Phase} \rightarrow \\_{Prop}$ (axiom)

$\\_{coherent} : \\_{Entity} \rightarrow \\_{Prop}$
$\\_{decoherent} : \\_{Entity} \rightarrow \\_{Prop}$
$\\_{stable} : \\_{Entity} \rightarrow \\_{Prop}$

$\\_{is\_ quantum} : \\_{List State} \rightarrow \\_{Prop}$
$\\_{is\_ classical} : \\_{List State} \rightarrow \\_{Prop}$
$\\_{coherent\_ state} : \\_{KLZ.State} \rightarrow \\_{Prop}$

$\\_{is\_ grounded} : \\_{Entity} \rightarrow \\_{Entity} \rightarrow \\_{Prop}$

---

### ENTITY CLASSIFICATION

**entity\_classification :**
$\forall e. (\\_{is\_ substrate}(e) \wedge e = \\_{Substrate}) \vee \\_{is\_ presentation}(e) \vee \\_{is\_ emergent}(e)$

$\\_{substrate\_ not\_ presentation} : \forall e. \neg(\\_{is\_ substrate}(e) \wedge \\_{is\_ presentation}(e))$
$\\_{substrate\_ not\_ emergent} : \forall e. \neg(\\_{is\_ substrate}(e) \wedge \\_{is\_ emergent}(e))$
$\\_{presentation\_ not\_ emergent} : \forall e. \neg(\\_{is\_ presentation}(e) \wedge \\_{is\_ emergent}(e))$

**presentation\_temporal\_or\_static :**
$\forall e. \\_{is\_ presentation}(e) \rightarrow$
$$(\\_{is\_ temporal\_ presentation}(e) \vee \\_{is\_ static\_ presentation}(e)) \wedge$$
$$\neg(\\_{is\_ temporal\_ presentation}(e) \wedge \\_{is\_ static\_ presentation}(e))$$

---

### SUBSTRATE PROPERTIES

$\\_{substrate\_ unique} : \forall x, y. \\_{is\_ substrate}(x) \wedge \\_{is\_ substrate}(y) \rightarrow x = y$
$\\_{substrate\_ is\_ Substrate} : \\_{is\_ substrate}(\\_{Substrate})$
$\\_{Omega\_ is\_ substrate} : \\_{is\_ substrate}(\Omega)$
$\\_{Omega\_ eq\_ Substrate} : \Omega = \\_{Substrate}$

---

### TEMPORAL PRESERVATION

**indexed\_preserves\_presentation :**
$\forall e, t. \\_{is\_ presentation}(e) \rightarrow \\_{is\_ presentation}(\\_{indexed}(e, t))$

**temporal\_slice\_preserves\_presentation :**
$\forall es, t. (\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow$
$$(\forall e \in \\_{temporal\_ slice}(es, t). \\_{is\_ presentation}(e))$$

---

### ASSOCIATIVITY

**join\_associative :**
$\forall s_1, s_2, s_3. \\_{join}([\\_{join}([s_1, s_2]), s_3]) = \\_{join}([s_1, \\_{join}([s_2, s_3])])$

---

### VERIFIED THEOREMS

**energy\_from\_complexity :**
$\forall e. \\_{is\_ presentation}(e) \rightarrow \\_{has\_ mass}(e) \rightarrow$
$$\exists m > 0. m = \\_{energy\_ of}(e)/c^2$$

**entropy\_from\_complexity :**
$\forall e. \\_{is\_ presentation}(e) \rightarrow \exists S.$
$$S = k_B \cdot \log(2) \cdot K(e)$$

**coherence\_participation\_invariant :**
$\forall e. \\_{is\_ temporal\_ presentation}(e) \rightarrow \\_{coherent}(e) \rightarrow$
$$0 < \\_{P\_ total}(e) \wedge \\_{Coh\_ trajectory}(e) = 1/\\_{P\_ total}(e)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow \\_{K\_ joint}(es) \leq \\_{K\_ sum}(es)$

**complexity\_subadditive :**
$\forall e_1, e_2. \\_{is\_ presentation}(e_1) \rightarrow \\_{is\_ presentation}(e_2) \rightarrow$
$$\\_{K\_ joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$

**compression\_ratio\_ge\_one :**
$\forall es, \\_{times}. (\forall e \in es. \\_{is\_ presentation}(e)) \rightarrow$
$$1 \leq \\_{Compression\_ ratio}(es, \\_{times})$$

**R\_G1\_preserves\_grounding :**
$\forall n. \\_{K\_ LZ}(\\_{mode}(\\_{join}(n))) < \\_{K\_ LZ}(\\_{join}(n)) + \\_{c\_ grounding}$

**time\_arrow\_reduction :**
$\forall \\_{hist}, n. \\_{K\_ LZ}(\\_{join}(\\_{mode}(\\_{join}(n))::\\_{hist})) \leq \\_{K\_ LZ}(\\_{join}(\\_{hist})) + \\_{c\_ time\_ reduction}$

**time\_arrow\_cohesion :**
$\forall \\_{hist}, n, h. \\_{K\_ LZ}(\\_{join}(\\_{R\_ Cohesion}(n, h)::\\_{hist})) \leq \\_{K\_ LZ}(\\_{join}(\\_{hist})) + \\_{c\_ time\_ cohesion}$

**P3\_C6\_preservation :**
$\forall n, h. \\_{coherent\_ state}(\\_{join}(n)) \rightarrow \\_{K\_ LZ}(\\_{R\_ G1}(n, h)) = \\_{K\_ LZ}(h)$

**R\_G1\_grounding\_reduction :**
$\forall n, h. \\_{K\_ LZ}(\\_{join}(n)) > \\_{c\_ grounding} \rightarrow$
$$\\_{K\_ LZ}(\\_{R\_ G1}(n, h)) < \\_{K\_ LZ}(\\_{join}(n)) + \\_{c\_ grounding}$$

**R\_G1\_preserves\_time\_arrow :**
$\forall \\_{hist}, n, h.$
$$\\_{K\_ LZ}(\\_{join}(\\_{R\_ G1}(n, h)::\\_{hist})) \leq \\_{K\_ LZ}(\\_{join}(\\_{Lz}(\\_{hist})) + \max(\\_{c\_ time\_ reduction}, \\_{c\_ time\_ cohesion})$$

**planck\_units\_positive :**
$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$

**error\_bound\_exists :**
$\forall e, p. \\_{is\_ presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| \leq \epsilon.\\_{absolute}$