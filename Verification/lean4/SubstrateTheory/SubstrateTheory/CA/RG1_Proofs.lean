
import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.CA.Mechanistic
import «Operational/KLZ/Core»

set_option autoImplicit false

namespace SubstrateTheory.CA

open SubstrateTheory.Operational


theorem R_G1_grounding_reduction_done
  (n : List State) (h : State)
  (h_gt_grounding : (K_LZ (join n) : ℝ) > c_grounding) :
  (K_LZ (R_G1 n h) : ℝ) < (K_LZ (join n) : ℝ) + c_grounding := by
  
  simp [R_G1, h_gt_grounding, R_Reduction]
  
  exact R_G1_preserves_grounding n

end SubstrateTheory.CA
