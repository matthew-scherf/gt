import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

namespace SubstrateTheory
abbrev State := List Bool
opaque Entity : Type

axiom Ω : Entity
abbrev Time := ℝ
abbrev Phase := ℝ
abbrev Nbhd := List State
abbrev Precision := ℕ

axiom Substrate : Entity
axiom is_substrate : Entity → Prop
axiom is_presentation : Entity → Prop
axiom is_emergent : Entity → Prop
axiom is_temporal_presentation : Entity → Prop
axiom is_static_presentation : Entity → Prop
axiom phenomenal : Entity → Prop
axiom has_mass : Entity → Prop
axiom is_quantum_state : Entity → Prop
axiom is_measurement_device : Entity → Prop
axiom is_observable : Entity → Prop
axiom indexed : Entity → Time → Entity
axiom temporally_indexed : Entity → Time → Prop
axiom static_value : Entity → Entity
axiom indexed_preserves_presentation : ∀ e t,
  is_presentation e → is_presentation (indexed e t)

axiom grounds : Entity → Entity → Prop
axiom temporal_grounds : Entity → Time → Entity → Time → Prop
axiom interacts : Entity → Entity → Prop
axiom inseparable : Entity → Entity → Prop
axiom emerges_from : Entity → List Entity → Prop
axiom phase_coupled : Entity → Entity → Phase → Prop
axiom depends_on : Entity → Time → Prop
axiom energy_of : Entity → ℝ
axiom mass : Entity → ℝ
axiom coupling_strength : Entity → Entity → ℝ
axiom phase_correlation : Entity → Entity → Phase

def complexity_sum_list (K : Entity → ℝ) : List Entity → ℝ
  | [] => 0
  | e :: es => K e + complexity_sum_list K es

noncomputable def temporal_slice (es : List Entity) (t : Time) : List Entity :=
  es.map (fun e => indexed e t)

lemma temporal_slice_preserves_presentation (es : List Entity) (t : Time) :
  (∀ e ∈ es, is_presentation e) →
  (∀ e ∈ temporal_slice es t, is_presentation e) := by
  intro h e he
  simp [temporal_slice] at he
  obtain ⟨e', he', rfl⟩ := he
  exact indexed_preserves_presentation e' t (h e' he')

axiom substrate_unique : ∀ x y, is_substrate x → is_substrate y → x = y
axiom substrate_is_Substrate : is_substrate Substrate
axiom Omega_is_substrate : is_substrate Ω
axiom Omega_eq_Substrate : Ω = Substrate
axiom entity_classification : ∀ e : Entity,
  (is_substrate e ∧ e = Substrate) ∨ is_presentation e ∨ is_emergent e

axiom substrate_not_presentation : ∀ e, ¬(is_substrate e ∧ is_presentation e)
axiom substrate_not_emergent : ∀ e, ¬(is_substrate e ∧ is_emergent e)
axiom presentation_not_emergent : ∀ e, ¬(is_presentation e ∧ is_emergent e)
axiom presentation_temporal_or_static : ∀ e,
  is_presentation e → (is_temporal_presentation e ∨ is_static_presentation e) ∧
                     ¬(is_temporal_presentation e ∧ is_static_presentation e)

axiom join : List State → State
axiom join_associative : ∀ s1 s2 s3, join [join [s1, s2], s3] = join [s1, join [s2, s3]]
open Classical in

noncomputable def slice (es : List (Entity × Time)) (T : Time) : List Entity :=
  letI : DecidableRel (fun (x y : ℝ) => x ≤ y) := Classical.decRel _
  (es.filter (fun p => p.2 ≤ T)).map (fun p => p.1)

end SubstrateTheory
