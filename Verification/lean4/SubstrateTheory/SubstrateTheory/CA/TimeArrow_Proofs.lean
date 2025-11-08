import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.CA.Mechanistic
import «Operational/KLZ/Core»
import «Operational/KLZ/TimeArrow»

set_option autoImplicit false

namespace SubstrateTheory.CA

open SubstrateTheory.Operational


def c_time : ℝ := max (c_time_reduction) (c_time_cohesion)

theorem R_G1_preserves_time_arrow_done
  (hist n : List State) (h : State) :
  let next := R_G1 n h
  K_LZ (join (next :: hist)) ≤ K_LZ (join hist) + c_time := by
  intro nextDef
  by_cases hle : (K_LZ (join n) : ℝ) ≤ c_grounding
  ·
    have : next = R_Cohesion n h := by simp [R_G1, nextDef, hle]
    calc
      K_LZ (join (next :: hist))
          = K_LZ (join (R_Cohesion n h :: hist)) := by simpa [this]
      _   ≤ K_LZ (join hist) + c_time_cohesion := time_arrow_cohesion hist n h
      _   ≤ K_LZ (join hist) + c_time := by
              have : c_time_cohesion ≤ c_time := by
                unfold c_time; apply le_max_right
              nlinarith
  ·
    have : next = R_Reduction n := by
      have hgt : (K_LZ (join n) : ℝ) > c_grounding := lt_of_not_ge hle
      simp [R_G1, nextDef, hgt, R_Reduction]
    calc
      K_LZ (join (next :: hist))
          = K_LZ (join (R_Reduction n :: hist)) := by simpa [this]
      _   ≤ K_LZ (join hist) + c_time_reduction := time_arrow_reduction hist n
      _   ≤ K_LZ (join hist) + c_time := by
              have : c_time_reduction ≤ c_time := by
                unfold c_time; apply le_max_left
              nlinarith

theorem R_G1_preserves_time_arrow
  (hist n : List State) (h : State) :
  let next := R_G1 n h
  K_LZ (join (next :: hist)) ≤ K_LZ (join hist) + c_time := by
  intro nextDef

  simpa [nextDef] using
    SubstrateTheory.CA.R_G1_preserves_time_arrow_done hist n h

end SubstrateTheory.CA
