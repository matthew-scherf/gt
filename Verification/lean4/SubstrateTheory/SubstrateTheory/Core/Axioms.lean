import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Ideal.Complexity
import Mathlib.Data.Real.Basic

namespace SubstrateTheory.Core
open SubstrateTheory SubstrateTheory.Ideal

def is_grounded (e ctx : Entity) : Prop :=
  K_cond ctx e < K e - K ctx + c_grounding

axiom G1_substrate_grounds_all : ∀ e,
  is_presentation e → is_grounded e Substrate

axiom T7_time_arrow : ∀ (hist : List Entity) (next : Entity),
  (∀ e ∈ hist, is_temporal_presentation e) →
  hist.length ≥ 2 →
  is_temporal_presentation next →
  ∀ (hist_last hist_init : Entity),
  hist.getLast? = some hist_last →
  hist.head? = some hist_init →
  let S_hist := K_joint hist
  let S_next := K_joint (next :: hist)
  let K_next_given_hist := S_next - S_hist
  let K_last_given_init := K_joint [hist_last, hist_init] - K hist_init
  K_next_given_hist ≤ K_last_given_init

def emergent (e_classical e_quantum : Entity) : Prop :=
  K_cond Substrate e_classical < K e_quantum

axiom T4_emergence_collapse : ∀ e_classical e_quantum,
  is_presentation e_classical →
  is_quantum_state e_quantum →
  emergent e_classical e_quantum →
  is_measurement_device e_classical ∨ is_observable e_classical

def coherent (e : Entity) : Prop :=
  ∀ t₁ t₂ : Time, t₁ < t₂ →
  is_temporal_presentation e →
  let e_t1 := indexed e t₁
  let e_t2 := indexed e t₂
  K_cond e_t1 e_t2 = K_cond e_t2 e_t1

axiom C6_coherence_preservation : ∀ e,
  is_quantum_state e → coherent e

def decoherent (e : Entity) : Prop := ¬coherent e

axiom decoherence_implies_classical : ∀ e,
  is_presentation e →
  decoherent e →
  ∃ t₀, ∀ t > t₀, ¬is_quantum_state (indexed e t)

axiom substrate_ultimate_ground : ∀ e,
  is_presentation e →
  ∃ path : List Entity,
    path.head? = some Substrate ∧
    path.getLast? = some e ∧
    ∀ i : ℕ, ∀ h1 : i < path.length, ∀ h2 : i + 1 < path.length,
      is_grounded (path[i+1]) (path[i])

axiom time_arrow_from_decoherence : ∀ e (hist : List Entity) next,
  coherent e →
  (∀ x ∈ hist, ∃ t, indexed e t = x) →
  decoherent next →
  ∃ ΔS, ΔS > 0

axiom measurement_breaks_coherence : ∀ e_q e_c,
  is_quantum_state e_q →
  coherent e_q →
  emergent e_c e_q →
  decoherent e_c

axiom classical_grounded_emergent : ∀ e,
  (∃ e_q, emergent e e_q) →
  is_grounded e Substrate

end SubstrateTheory.Core
