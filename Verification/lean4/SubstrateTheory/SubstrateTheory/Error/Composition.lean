import SubstrateTheory.Error.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SubstrateTheory.Error

open SubstrateTheory

def compose_additive (ε₁ ε₂ : ℝ) : ℝ :=
  ε₁ + ε₂

noncomputable def compose_multiplicative (ε K_max : ℝ) : ℝ :=
  Real.exp (ε * K_max) - 1

theorem additive_composition_bound (ε₁ ε₂ : ℝ) (h₁ : 0 ≤ ε₁) (h₂ : 0 ≤ ε₂) :
  ε₁ ≤ compose_additive ε₁ ε₂ ∧ ε₂ ≤ compose_additive ε₁ ε₂ := by
  constructor
  · simp [compose_additive]
    linarith
  · simp [compose_additive]
    linarith

theorem multiplicative_composition_bound (ε K_max : ℝ) (hε : 0 ≤ ε) (hK : 0 < K_max) :
  ε * K_max ≤ compose_multiplicative ε K_max := by
  simp [compose_multiplicative]
  have h : ε * K_max + 1 ≤ Real.exp (ε * K_max) := Real.add_one_le_exp (ε * K_max)
  linarith

end SubstrateTheory.Error
