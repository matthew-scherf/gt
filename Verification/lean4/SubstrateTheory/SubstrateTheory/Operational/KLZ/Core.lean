
import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters

set_option autoImplicit false

namespace SubstrateTheory.Operational


constant State : Type
constant join  : List State → State


noncomputable constant mode : State → State


noncomputable constant K_LZ : State → ℝ


constant c_grounding : ℝ




axiom K_LZ_nonneg (s : State) : 0 ≤ K_LZ s


constant c_sub : ℝ
axiom K_LZ_subadditive_cons
  (x : State) (xs : List State) :
  K_LZ (join (x :: xs)) ≤ K_LZ (join xs) + K_LZ x + c_sub


axiom K_LZ_prefix
  (b : State) (s : List State) :
  K_LZ (join [b]) ≤ K_LZ (join (b :: s))


constant c_single : ℝ
axiom K_LZ_singleton_bound : ∀ b : State, K_LZ (join [b]) ≤ c_single


constant C_mode : ℝ
axiom K_LZ_mode_le (s : State) :
  K_LZ (mode s) ≤ K_LZ s + C_mode


axiom C_mode_lt_c_grounding : C_mode < c_grounding




theorem R_G1_preserves_grounding (n : List State) :
  K_LZ (mode (join n)) < K_LZ (join n) + c_grounding := by
  have h := K_LZ_mode_le (join n)
  have hlt : K_LZ (join n) + C_mode < K_LZ (join n) + c_grounding := by
    exact add_lt_add_left C_mode_lt_c_grounding (K_LZ (join n))
  exact lt_of_le_of_lt h hlt

end SubstrateTheory.Operational
