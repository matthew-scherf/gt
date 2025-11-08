import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
namespace SubstrateTheory.Ideal

open SubstrateTheory

noncomputable axiom K : Entity → ℝ

noncomputable def K_sum (es : List Entity) : ℝ :=
  (es.map K).sum

@[simp] lemma K_sum_nil : K_sum [] = 0 := by
  simp [K_sum]

@[simp] lemma K_sum_cons (e : Entity) (es : List Entity) :
    K_sum (e :: es) = K e + K_sum es := by
  simp [K_sum]

@[simp] lemma K_sum_singleton (e : Entity) : K_sum [e] = K e := by
  simp [K_sum]

@[simp] lemma K_sum_pair (e₁ e₂ : Entity) : K_sum [e₁, e₂] = K e₁ + K e₂ := by
  simp [K_sum]

noncomputable axiom K_joint : List Entity → ℝ

axiom K_joint_nonneg : ∀ es, 0 ≤ K_joint es

axiom K_joint_nil : K_joint [] = 0

axiom K_joint_singleton : ∀ e, K_joint [e] = K e

noncomputable def K_cond (e₁ e₂ : Entity) : ℝ :=
  K_joint [e₁, e₂] - K e₁

axiom complexity_positive : ∀ e, is_presentation e → 0 < K e

axiom substrate_complexity : K Substrate = 0
axiom K2_substrate_minimality : K Ω = 0

axiom substrate_minimal : ∀ e, is_presentation e → K Substrate ≤ K e

axiom compression_axiom : ∀ (es : List Entity),
  (∀ e ∈ es, is_presentation e) →
  es.length ≥ 2 →
  K_joint es < K_sum es

theorem joint_le_sum (es : List Entity) :
  (∀ e ∈ es, is_presentation e) →
  K_joint es ≤ K_sum es := by
  intro h
  by_cases h2 : es.length < 2
  · cases es with
    | nil =>
      simp [K_sum, K_joint_nil]
    | cons e es' =>
      cases es' with
      | nil =>
        simp [K_sum, K_joint_singleton]
      | cons e' es'' =>
        simp at h2
        omega
  · push_neg at h2
    exact le_of_lt (compression_axiom es h h2)

axiom conditional_reduction : ∀ e₁ e₂,
  is_presentation e₁ → is_presentation e₂ →
  ∃ r : ℝ, r ≥ 0 ∧ K e₂ ≥ (1 + r) * K_cond e₁ e₂

noncomputable def Coh (es : List Entity) (times : List Time) : ℝ :=
  if h : K_sum (times.flatMap (temporal_slice es)) = 0 then 0
  else 1 - K_joint (times.flatMap (temporal_slice es)) / K_sum (times.flatMap (temporal_slice es))

axiom coherence_bounds : ∀ es times,
  (∀ e ∈ es, is_presentation e) →
  0 ≤ Coh es times ∧ Coh es times ≤ 1

noncomputable def Coh_t (e : Entity) (t : Time) : ℝ :=
  Coh [e] [t]

noncomputable def dCoh_dt (e : Entity) (t : Time) : ℝ :=
  deriv (coh_t_func e) t

noncomputable def compression_ratio (es : List Entity) (times : List Time) : ℝ :=
  let joint := K_joint (times.flatMap (temporal_slice es))
  if joint = 0 then 1 else K_sum (times.flatMap (temporal_slice es)) / joint

theorem compression_ratio_ge_one (es : List Entity) (times : List Time) :
  (∀ e ∈ es, is_presentation e) →
  1 ≤ compression_ratio es times := by
  intro h
  simp only [compression_ratio]
  split
  · norm_num
  · rename_i h_ne
    rw [one_le_div_iff]
    left
    constructor
    · by_contra h_neg
      push_neg at h_neg
      have h_eq : K_joint (times.flatMap (temporal_slice es)) = 0 := by
        have := K_joint_nonneg (times.flatMap (temporal_slice es))
        linarith
      exact h_ne h_eq
    · have hpres : ∀ e ∈ times.flatMap (temporal_slice es), is_presentation e := by
        intro e he
        simp [List.mem_flatMap] at he
        obtain ⟨t, _, he'⟩ := he
        exact temporal_slice_preserves_presentation es t h e he'
      exact joint_le_sum (times.flatMap (temporal_slice es)) hpres

axiom emergence_complexity : ∀ x C,
  emerges_from x C →
  K_joint C < K x ∧ K x < K_sum C

axiom energy_complexity : ∀ e,
  is_presentation e → energy_of e = κ_energy * K e

axiom complexity_additive : ∀ e₁ e₂,
  is_presentation e₁ → is_presentation e₂ →
  inseparable e₁ e₂ = False →
  K_joint [e₁, e₂] = K e₁ + K e₂

theorem K_joint_le_sum_pair
  {e₁ e₂ : Entity}
  (h1 : is_presentation e₁)
  (h2 : is_presentation e₂) :
  K_joint [e₁, e₂] ≤ K e₁ + K e₂ := by
  have hpres : ∀ e ∈ ([e₁, e₂] : List Entity), is_presentation e := by
    intro e he
    simp [List.mem_cons] at he
    cases he with
    | inl heq => rw [heq]; exact h1
    | inr heq => rw [heq]; exact h2
  have := joint_le_sum [e₁, e₂] hpres
  rw [K_sum_pair] at this
  exact this

theorem complexity_subadditive (e₁ e₂ : Entity) :
  is_presentation e₁ → is_presentation e₂ →
  K_joint [e₁, e₂] ≤ K e₁ + K e₂ := by
  intro h1 h2
  exact K_joint_le_sum_pair h1 h2

axiom joint_monotone : ∀ (es : List Entity) (e : Entity),
  is_presentation e →
  (∀ x ∈ es, is_presentation x) →
  K_joint es ≤ K_joint (e :: es)

end SubstrateTheory.Ideal
