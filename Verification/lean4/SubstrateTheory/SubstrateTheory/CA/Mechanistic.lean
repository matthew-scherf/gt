import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import Mathlib.Data.List.Basic
import SubstrateTheory.Operational.KLZ.Core
import SubstrateTheory.Operational.KLZ.TimeArrow

namespace SubstrateTheory.CA
open SubstrateTheory SubstrateTheory.Operational
abbrev State := KLZ.KLZState

noncomputable def F (s : State) : State := s
noncomputable def merge (s1 s2 : State) : State := s2
noncomputable def R_Cohesion (n : List State) (h : State) : State :=
  merge (F (KLZ.join n)) h

noncomputable def R_Reduction (n : List State) : State :=
  KLZ.mode (KLZ.join n)

noncomputable def R_G1 (n : List State) (h : State) : State :=
  if (KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding then
    R_Cohesion n h
  else
    R_Reduction n

noncomputable def coherent_state (s : State) : Prop :=
  (KLZ.K_LZ s : ℝ) ≤ c_grounding

theorem P3_C6_preservation : ∀ n h,
  coherent_state (KLZ.join n) →
  KLZ.K_LZ (R_G1 n h) = KLZ.K_LZ h := by
  intros n h h_coherent
  simp only [coherent_state] at h_coherent
  simp only [R_G1, h_coherent]
  simp [R_Cohesion, F, merge]

theorem R_G1_grounding_reduction
  (n : List State) (h : State)
  (h_gt_grounding : (KLZ.K_LZ (KLZ.join n) : ℝ) > c_grounding) :
  (KLZ.K_LZ (R_G1 n h) : ℝ) < (KLZ.K_LZ (KLZ.join n) : ℝ) + c_grounding := by
  simp only [R_G1]
  have : ¬((KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding) := by linarith
  simp only [this, ite_false, R_Reduction]
  exact KLZ.R_G1_preserves_grounding n

end SubstrateTheory.CA
