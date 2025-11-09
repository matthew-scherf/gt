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
  obtain ⟨c, hc_pos, hc_bound⟩ := error_bound_linear
  use c, hc_pos
  intro p hp
  exact hc_bound e p he hp

theorem convergence_rate_polynomial_alt : ∀ e,
  is_presentation e →
  ∃ c α : ℝ, 0 < c ∧ 1 < α ∧
  ∀ p : ℕ, 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ)^α := by
  intro e he
  obtain ⟨c, α, hc_pos, hα_gt, hbound⟩ := error_bound_polynomial
  use c, α, hc_pos, hα_gt
  intro p hp
  exact hbound e p he hp

end SubstrateTheory.Error
