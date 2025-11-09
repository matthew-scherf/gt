import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.CA.Mechanistic
import SubstrateTheory.Operational.KLZ.Core
set_option autoImplicit false

namespace SubstrateTheory.CA
open SubstrateTheory.Core SubstrateTheory.Operational

theorem R_G1_grounding_reduction_done
  (n : List State) (h : State)
  (h_gt_grounding : (KLZ.K_LZ (KLZ.join n) : ℝ) > c_grounding) :
  (KLZ.K_LZ (R_G1 n h) : ℝ) < (KLZ.K_LZ (KLZ.join n) : ℝ) + c_grounding := by
  simp only [R_G1]
  have : ¬((KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding) := by linarith
  simp only [this, ite_false]
  exact KLZ.R_G1_preserves_grounding n

end SubstrateTheory.CA
