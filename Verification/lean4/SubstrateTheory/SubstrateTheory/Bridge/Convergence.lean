import SubstrateTheory.Ideal.Complexity
import SubstrateTheory.Operational.Complexity
import SubstrateTheory.Core.Grounding
import Mathlib.Topology.MetricSpace.Basic

namespace SubstrateTheory.Bridge

open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational SubstrateTheory.Core

axiom BRIDGE1 : ∀ e, is_presentation e → 
  ∀ ε : ℝ, 0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  abs (C e p - K e) < ε

axiom C_upper_bound : ∀ e p,
  is_presentation e → K e ≤ C e p

theorem C_bounds_K (e : Entity) (p : Precision) :
  is_presentation e → K e ≤ C e p :=
  C_upper_bound e p

theorem error_nonneg (e : Entity) (p : Precision) :
  is_presentation e → 0 ≤ C e p - K e := by
  intro h
  exact sub_nonneg_of_le (C_bounds_K e p h)

axiom BRIDGE2 : ∀ (S : Finset Entity) (ε : ℝ),
  (∀ e ∈ S, is_presentation e) →
  0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  ∀ e ∈ S, abs (C e p - K e) < ε

noncomputable def Z_ideal (S : Finset Entity) : ℝ :=
  S.sum (fun e => 2^(-(K e)))

noncomputable def Z_op (S : Finset Entity) (p : Precision) : ℝ :=
  S.sum (fun e => 2^(-(C e p)))

axiom BRIDGE3 : ∀ (S : Finset Entity) (ε : ℝ),
  (∀ e ∈ S, is_presentation e) →
  0 < ε →
  0 < Z_ideal S →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  abs (Z_op S p - Z_ideal S) / Z_ideal S < ε

def grounds_K (e₁ e₂ : Entity) : Prop :=
  K_cond e₁ e₂ < K e₂ - K e₁ + c_grounding

axiom BRIDGE4 : ∀ (S : Finset Entity) (ε : ℝ) (e₁ e₂ : Entity),
  e₁ ∈ S → e₂ ∈ S →
  is_presentation e₁ → is_presentation e₂ →
  0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  (grounds_K e₁ e₂ ↔ grounds_C e₁ e₂ p)

axiom BRIDGE5 : ∀ (S : Finset Entity) (e : Entity),
  e ∈ S →
  is_presentation e →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  rank_C e p = rank_K e

noncomputable def Coh_op (es : List Entity) (times : List Time) (p : Precision) : ℝ :=
  let sliced := times.flatMap (temporal_slice es)
  let joint := C_joint sliced p
  let sum := C_sum sliced p
  if sum = 0 then 0 else 1 - joint / sum

axiom BRIDGE6 : ∀ (e : Entity) (times : List Time) (ε : ℝ),
  is_temporal_presentation e →
  0 < ε →
  ∃ p₀ : ℕ, ∃ δ : ℝ, ∀ p : ℕ, p ≥ p₀ →
  ∀ t ∈ times,
    abs (Coh_op [e] [t] p - Coh [e] [t]) < ε

axiom BRIDGE6_general : ∀ (es : List Entity) (times : List Time) (ε : ℝ),
  (∀ e ∈ es, is_temporal_presentation e) →
  0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
    abs (Coh_op es times p - Coh es times) < ε

axiom BRIDGE6_static : ∀ (es : List Entity) (times : List Time) (ε : ℝ),
  (∀ e ∈ es, is_presentation e) →
  (∃ e ∈ es, is_static_presentation e) →
  0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
    abs (Coh_op es times p - Coh es times) < ε

axiom BRIDGE7 : ∀ (e₁ e₂ : Entity) (ε : ℝ),
  is_presentation e₁ → is_presentation e₂ →
  0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  abs (C_cond e₁ e₂ p - K_cond e₁ e₂) < ε

axiom BRIDGE7_joint : ∀ (es : List Entity) (ε : ℝ),
  (∀ e ∈ es, is_presentation e) →
  0 < ε →
  ∃ p₀ : ℕ, ∀ p : ℕ, p ≥ p₀ →
  abs (C_joint es p - K_joint es) < ε

noncomputable def dCoh_dt (e : Entity) (t : Time) : ℝ :=
  Classical.epsilon (fun rate => 
    ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < |h| → |h| < δ → 
      |Coh [e] [t + h] - Coh [e] [t] - rate * h| / |h| < ε)

axiom BRIDGE8 : ∀ (e : Entity) (times : List Time) (ε : ℝ),
  is_temporal_presentation e →
  0 < ε →
  ∃ p₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℕ, p ≥ p₀ →
  ∀ t ∈ times,
    abs ((Coh_op [e] [t + δ] p - Coh_op [e] [t] p) / δ - dCoh_dt e t) < ε

theorem joint_convergence (es : List Entity) :
  (∀ e ∈ es, is_presentation e) →
  ∀ ε : ℝ, 0 < ε →
  ∃ p₀ : ℕ, ∀ p ≥ p₀,
  abs (C_joint es p - K_joint es) < ε := by
  intro hpres ε hε
  exact BRIDGE7_joint es ε hpres hε

theorem coherence_convergence (es : List Entity) (times : List Time) :
  (∀ e ∈ es, is_presentation e) →
  ∀ ε : ℝ, 0 < ε →
  ∃ p₀ : ℕ, ∀ p ≥ p₀,
  abs (Coh_op es times p - Coh es times) < ε := by
  intro hpres ε hε
  by_cases h : ∀ e ∈ es, is_temporal_presentation e
  · exact BRIDGE6_general es times ε h hε
  · push_neg at h
    obtain ⟨e, he_mem, he_not_temp⟩ := h
    have he_pres := hpres e he_mem
    have ⟨he_temp_or_static, _⟩ := presentation_temporal_or_static e he_pres
    cases he_temp_or_static with
    | inl h_temp => contradiction
    | inr h_static =>
      apply BRIDGE6_static es times ε hpres
      · exact ⟨e, he_mem, h_static⟩
      · exact hε

end SubstrateTheory.Bridge
