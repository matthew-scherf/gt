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
    abs_nonneg := by
      apply div_nonneg
      · norm_num
      · apply le_of_lt
        exact Nat.cast_add_one_pos p
    rel_nonneg := by
      apply div_nonneg
      · norm_num
      · apply le_of_lt
        exact Nat.cast_add_one_pos p }

axiom error_bound_linear : ∃ c : ℝ, 0 < c ∧
  ∀ e p, is_presentation e → 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ)

axiom error_bound_polynomial : ∃ c α : ℝ, 0 < c ∧ 1 < α ∧
  ∀ e p, is_presentation e → 0 < p →
  abs (C e p - K e) ≤ c / (p : ℝ)^α

axiom error_bound_general : ∃ M : ℝ, 0 < M ∧
  ∀ e p, is_presentation e →
  abs (C e p - K e) ≤ M / (p + 1 : ℝ)

theorem error_bound_exists : ∀ e p,
  is_presentation e →
  ∃ ε : ErrorBound, abs (C e p - K e) ≤ ε.absolute := by
  intro e p h
  obtain ⟨M, hM_pos, hM_bound⟩ := error_bound_general
  use { absolute := M / (p + 1 : ℝ)
        relative := M / (p + 1 : ℝ)
        precision := p
        abs_nonneg := by
          apply div_nonneg
          · apply le_of_lt
            exact hM_pos
          · apply le_of_lt
            exact Nat.cast_add_one_pos p
        rel_nonneg := by
          apply div_nonneg
          · apply le_of_lt
            exact hM_pos
          · apply le_of_lt
            exact Nat.cast_add_one_pos p }
  exact hM_bound e p h

end SubstrateTheory.Error
