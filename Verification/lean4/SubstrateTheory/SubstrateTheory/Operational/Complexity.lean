import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace SubstrateTheory.Operational

open SubstrateTheory

noncomputable axiom C : Entity → ℕ → ℝ

axiom C_nonneg : ∀ e p, 0 ≤ C e p

axiom C_monotone : ∀ e p₁ p₂, p₁ ≤ p₂ → C e p₂ ≤ C e p₁

noncomputable def C_sum (es : List Entity) (p : ℕ) : ℝ :=
  (es.map (fun e => C e p)).sum

@[simp] lemma C_sum_nil (p : ℕ) : C_sum [] p = 0 := by
  simp [C_sum]

@[simp] lemma C_sum_cons (e : Entity) (es : List Entity) (p : ℕ) :
    C_sum (e :: es) p = C e p + C_sum es p := by
  simp [C_sum]

noncomputable axiom C_joint : List Entity → ℕ → ℝ

axiom C_joint_nonneg : ∀ es p, 0 ≤ C_joint es p

noncomputable def C_cond (e₁ e₂ : Entity) (p : ℕ) : ℝ :=
  C_joint [e₁, e₂] p - C e₁ p

axiom K_LZ : State → ℕ

axiom K_LZ_nonneg : ∀ s, 0 ≤ K_LZ s

axiom K_LZ_empty : K_LZ [] = 0

axiom K_LZ_monotone : ∀ s1 s2, s1.length ≤ s2.length → K_LZ s1 ≤ K_LZ s2

def is_quantum (nbhd : List State) : Prop := (K_LZ (join nbhd) : ℝ) ≤ c_grounding

def is_classical (nbhd : List State) : Prop := (K_LZ (join nbhd) : ℝ) > c_grounding

noncomputable def K_toy (s : State) : ℕ :=
  s.dedup.length  

axiom K_toy_lower_bound : ∀ s, K_LZ s ≤ K_toy s

axiom K_toy_upper_bound : ∀ s, K_toy s ≤ K_LZ s + (Nat.log 2 s.length)

end SubstrateTheory.Operational
