import SubstrateTheory.Bridge.Convergence
import SubstrateTheory.Core.Grounding
import Mathlib.Data.Real.Basic

namespace SubstrateTheory.Bridge
open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational SubstrateTheory.Core

noncomputable def coupling_strength_op (e₁ e₂ : Entity) (p : ℕ) : ℝ :=
  1 - C_joint [e₁, e₂] p / (C e₁ p + C e₂ p)

axiom coupling_convergence : ∀ (e₁ e₂ : Entity),
  is_presentation e₁ → is_presentation e₂ →
  ∀ ε : ℝ, 0 < ε →
  ∃ p₀ : ℕ, ∀ p ≥ p₀,
  abs (coupling_strength_op e₁ e₂ p - coupling_strength e₁ e₂) < ε

axiom inseparability_preserved : ∀ (e₁ e₂ : Entity),
  is_presentation e₁ → is_presentation e₂ →
  ∃ p₀ : ℕ, ∀ p ≥ p₀,
  (inseparable e₁ e₂ ↔
    C_joint [e₁, e₂] p / (C e₁ p + C e₂ p) < measured_inseparability_threshold)

end SubstrateTheory.Bridge
