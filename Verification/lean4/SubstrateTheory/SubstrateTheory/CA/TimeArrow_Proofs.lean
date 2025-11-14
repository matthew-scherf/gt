import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.Operational.KLZ.Core
import SubstrateTheory.Operational.KLZ.TimeArrow
set_option autoImplicit false

namespace SubstrateTheory.CA
open SubstrateTheory.Core SubstrateTheory.Operational
abbrev State := KLZ.State

axiom K_LZ_cohesion_preserves_h : ∀ (n : List State) (h : State),
  (KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding →
  KLZ.K_LZ (R_Cohesion n h) = KLZ.K_LZ h

noncomputable def R_G1 (n : List State) (h : State) : State :=
  if (KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding then
    R_Cohesion n h
  else
    KLZ.mode (KLZ.join n)

noncomputable def coherent_state (s : State) : Prop :=
  (KLZ.K_LZ s : ℝ) ≤ c_grounding

noncomputable def c_time : ℝ := max c_time_reduction c_time_cohesion

theorem P3_C6_preservation : ∀ n h,
  coherent_state (KLZ.join n) →
  KLZ.K_LZ (R_G1 n h) = KLZ.K_LZ h := by
  intros n h h_coherent
  simp only [coherent_state] at h_coherent
  simp only [R_G1, h_coherent, ite_true]
  exact K_LZ_cohesion_preserves_h n h h_coherent

theorem CA_K_empty : KLZ.K_LZ (KLZ.join []) = 0 :=
  KLZ.K_LZ_empty

theorem R_G1_grounding_reduction
  (n : List State) (h : State)
  (h_gt_grounding : (KLZ.K_LZ (KLZ.join n) : ℝ) > c_grounding) :
  (KLZ.K_LZ (R_G1 n h) : ℝ) < (KLZ.K_LZ (KLZ.join n) : ℝ) + c_grounding := by
  simp only [R_G1]
  have : ¬((KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding) := by linarith
  simp only [this, ite_false]
  exact KLZ.R_G1_preserves_grounding n

theorem R_G1_preserves_time_arrow
  (hist n : List State) (h : State) :
  (KLZ.K_LZ (KLZ.join (R_G1 n h :: hist)) : ℝ) ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time := by
  by_cases hle : (KLZ.K_LZ (KLZ.join n) : ℝ) ≤ c_grounding
  ·
    have h_eq : R_G1 n h = R_Cohesion n h := by
      simp only [R_G1, hle, ite_true]
    calc (KLZ.K_LZ (KLZ.join (R_G1 n h :: hist)) : ℝ)
        = (KLZ.K_LZ (KLZ.join (R_Cohesion n h :: hist)) : ℝ) := by rw [h_eq]
      _ ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time_cohesion := time_arrow_cohesion hist n h
      _ ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time := by
          gcongr
          exact le_max_right _ _
  ·
    have hgt : (KLZ.K_LZ (KLZ.join n) : ℝ) > c_grounding := by linarith
    have h_eq : R_G1 n h = KLZ.mode (KLZ.join n) := by
      simp only [R_G1, hle, ite_false]
    calc (KLZ.K_LZ (KLZ.join (R_G1 n h :: hist)) : ℝ)
        = (KLZ.K_LZ (KLZ.join (KLZ.mode (KLZ.join n) :: hist)) : ℝ) := by rw [h_eq]
      _ ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time_reduction := time_arrow_reduction hist n
      _ ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time := by
          gcongr
          exact le_max_left _ _

end SubstrateTheory.CA
