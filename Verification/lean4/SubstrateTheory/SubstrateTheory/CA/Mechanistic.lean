import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import Mathlib.Data.List.Basic


import SubstrateTheory.Operational.KLZ.Core
import SubstrateTheory.Operational.KLZ.TimeArrow


namespace SubstrateTheory.CA

open SubstrateTheory SubstrateTheory.Operational






noncomputable def F (s : State) : State :=
  s


noncomputable def merge (s1 s2 : State) : State :=
  s1








noncomputable def R_Cohesion (n : List State) (h : State) : State :=
  merge (F (join n)) h

noncomputable def R_Reduction (n : List State) : State :=
  mode (join n)

noncomputable def R_G1 (n : List State) (h : State) : State :=
  if (K_LZ (join n) : ℝ) ≤ c_grounding then
    R_Cohesion n h
  else
    R_Reduction n





noncomputable def coherent_state (s : State) : Prop :=
  (K_LZ s : ℝ) ≤ c_grounding


axiom P3_C6_preservation : ∀ n h,
  coherent_state (join n) →
  K_LZ (R_G1 n h) = K_LZ h






theorem CA_K_empty : K_LZ (join []) = 0 :=
  K_LZ_empty


theorem R_G1_grounding_reduction
  (n : List State) (h : State)
  (h_gt_grounding : (K_LZ (join n) : ℝ) > c_grounding) :
  (K_LZ (R_G1 n h) : ℝ) < (K_LZ (join n) : ℝ) + c_grounding := by

  simp [R_G1, h_gt_grounding, R_Reduction]

  exact SubstrateTheory.Operational.R_G1_preserves_grounding n

end SubstrateTheory.CA
