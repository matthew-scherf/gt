import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import Mathlib.Data.Real.Basic
set_option autoImplicit false

namespace SubstrateTheory.Operational.KLZ

axiom State : Type
axiom join  : List State → State
noncomputable axiom mode : State → State
noncomputable axiom K_LZ : State → ℕ

axiom c_sub : ℝ
axiom c_single : ℝ
axiom C_mode : ℝ
axiom K_LZ_nonneg (s : State) : 0 ≤ K_LZ s
axiom K_LZ_empty : K_LZ (join []) = 0
axiom K_LZ_subadditive_cons
  (x : State) (xs : List State) :
  (K_LZ (join (x :: xs)) : ℝ) ≤ (K_LZ (join xs) : ℝ) + (K_LZ x : ℝ) + c_sub

axiom K_LZ_prefix
  (b : State) (s : List State) :
  K_LZ (join [b]) ≤ K_LZ (join (b :: s))

axiom K_LZ_singleton_bound : ∀ b : State, (K_LZ (join [b]) : ℝ) ≤ c_single
axiom K_LZ_mode_le (s : State) :
  (K_LZ (mode s) : ℝ) ≤ (K_LZ s : ℝ) + C_mode

axiom C_mode_lt_c_grounding : C_mode < c_grounding

theorem R_G1_preserves_grounding (n : List State) :
  (K_LZ (mode (join n)) : ℝ) < (K_LZ (join n) : ℝ) + c_grounding := by
  have h := K_LZ_mode_le (join n)
  have hlt : (K_LZ (join n) : ℝ) + C_mode < (K_LZ (join n) : ℝ) + c_grounding := by
    exact add_lt_add_left C_mode_lt_c_grounding (K_LZ (join n) : ℝ)
  exact lt_of_le_of_lt h hlt

end SubstrateTheory.Operational.KLZ
