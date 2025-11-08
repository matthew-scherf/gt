import SubstrateTheory.Ideal.Complexity
import SubstrateTheory.Operational.Complexity
import Mathlib.Data.Real.Basic

namespace SubstrateTheory.Error

open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational

structure ErrorBound where
  absolute : ℝ
  relative : ℝ
  precision : ℕ
  abs_nonneg : 0 ≤ absolute
  rel_nonneg : 0 ≤ relative

noncomputable def DefaultErrorBound (p : ℕ) : ErrorBound :=
  { absolute := 1 / (p + 1 : ℝ)
    relative := 1 / (p + 1 : ℝ)
    precision := p
    abs_nonneg := by positivity
    rel_nonneg := by positivity }

axiom error_bound_linear : ∃ c : ℝ, 0 < c ∧
  ∀ e p, is_presentation e → 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ)

axiom error_bound_polynomial : ∃ c α : ℝ, 0 < c ∧ 1 < α ∧
  ∀ e p, is_presentation e → 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ)^α

theorem error_bound_exists : ∀ e p,
  is_presentation e →
  ∃ ε : ErrorBound, abs (C e p - K e) ≤ ε.absolute := by
  intro e p h
  obtain ⟨c, hc_pos, hc_bound⟩ := error_bound_linear
  by_cases hp : 0 < p
  · use { absolute := c / (p : ℝ)
          relative := c / (p : ℝ) 
          precision := p
          abs_nonneg := by positivity
          rel_nonneg := by positivity }
    exact hc_bound e p h hp
  · use DefaultErrorBound p
    simp [DefaultErrorBound]
    have : p = 0 := by omega
    simp [this]
    exact abs_nonneg _

end SubstrateTheory.Error
