import SubstrateTheory.Error.Bounds
import SubstrateTheory.Error.Composition
import SubstrateTheory.Bridge.Convergence
import Mathlib.Data.Real.Basic

namespace SubstrateTheory.Error

open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational SubstrateTheory.Bridge

theorem convergence_rate_linear : ∀ e,
  is_presentation e →
  ∃ c : ℝ, 0 < c ∧
  ∀ p : ℕ, 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ) := by
  intro e he
  exact error_bound_linear

theorem convergence_rate_polynomial_alt : ∀ e,
  is_presentation e →
  ∃ c α : ℝ, 0 < c ∧ 1 < α ∧
  ∀ p : ℕ, 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ)^α := by
  intro e he
  exact error_bound_polynomial

end SubstrateTheory.Error
