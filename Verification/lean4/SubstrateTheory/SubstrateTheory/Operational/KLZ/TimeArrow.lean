import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Operational.KLZ.Core
set_option autoImplicit false

namespace SubstrateTheory.Operational
noncomputable axiom R_Cohesion : List KLZ.KLZState → KLZ.KLZState → KLZ.KLZState

axiom C_coh : ℝ
axiom K_LZ_cohesion_bound_raw (n : List KLZ.KLZState) (h : KLZ.KLZState) :
  KLZ.K_LZ (R_Cohesion n h) ≤ C_coh

axiom K_LZ_mode_absolute_bound : ∀ s, (KLZ.K_LZ (KLZ.mode s) : ℝ) ≤ KLZ.C_mode

noncomputable def c_time_reduction : ℝ := KLZ.c_sub + KLZ.C_mode
noncomputable def c_time_cohesion  : ℝ := KLZ.c_sub + C_coh

theorem time_arrow_reduction (hist n : List KLZ.KLZState) :
  (KLZ.K_LZ (KLZ.join (KLZ.mode (KLZ.join n) :: hist)) : ℝ)
    ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time_reduction := by
  unfold c_time_reduction
  have h_sub := KLZ.K_LZ_subadditive_cons (KLZ.mode (KLZ.join n)) hist
  have h_mode := K_LZ_mode_absolute_bound (KLZ.join n)
  calc (KLZ.K_LZ (KLZ.join (KLZ.mode (KLZ.join n) :: hist)) : ℝ)
      ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + (KLZ.K_LZ (KLZ.mode (KLZ.join n)) : ℝ) + KLZ.c_sub := h_sub
    _ ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + KLZ.C_mode + KLZ.c_sub := by linarith [h_mode]
    _ = (KLZ.K_LZ (KLZ.join hist) : ℝ) + (KLZ.c_sub + KLZ.C_mode) := by ring

theorem time_arrow_cohesion (hist n : List KLZ.KLZState) (h : KLZ.KLZState) :
  (KLZ.K_LZ (KLZ.join (R_Cohesion n h :: hist)) : ℝ)
    ≤ (KLZ.K_LZ (KLZ.join hist) : ℝ) + c_time_cohesion := by
  unfold c_time_cohesion
  have h_sub := KLZ.K_LZ_subadditive_cons (R_Cohesion n h) hist
  have h_bnd := K_LZ_cohesion_bound_raw n h
  linarith

end SubstrateTheory.Operational
