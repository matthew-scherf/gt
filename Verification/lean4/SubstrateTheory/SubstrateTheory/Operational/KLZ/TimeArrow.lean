
import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import «Operational/KLZ/Core»

set_option autoImplicit false

namespace SubstrateTheory.Operational

open SubstrateTheory.Operational


noncomputable constant R_Cohesion : List State → State → State


constant C_coh : ℝ
axiom K_LZ_cohesion_bound_raw (n : List State) (h : State) :
  K_LZ (R_Cohesion n h) ≤ C_coh


def c_time_reduction : ℝ := c_sub + C_mode
def c_time_cohesion  : ℝ := c_sub + C_coh


theorem time_arrow_reduction
  (hist n : List State) :
  K_LZ (join (mode (join n) :: hist))
    ≤ K_LZ (join hist) + c_time_reduction := by
  
  have h_sub := K_LZ_subadditive_cons (mode (join n)) hist
  
  have h_mode_bnd := K_LZ_mode_le (join n)
  
  have h_nonneg := K_LZ_nonneg (join n)
  
  simp [c_time_reduction] at *
  
  
  
  
  
  
  
  
  nlinarith


theorem time_arrow_cohesion
  (hist n : List State) (h : State) :
  K_LZ (join (R_Cohesion n h :: hist))
    ≤ K_LZ (join hist) + c_time_cohesion := by
  
  have h_sub := K_LZ_subadditive_cons (R_Cohesion n h) hist
  have h_bnd := K_LZ_cohesion_bound_raw n h
  simp [c_time_cohesion] at *
  nlinarith

end SubstrateTheory.Operational
