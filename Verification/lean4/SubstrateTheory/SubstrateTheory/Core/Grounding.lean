
import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.Ideal.Complexity
import SubstrateTheory.Operational.Complexity
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card


namespace SubstrateTheory.Core

open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational

noncomputable axiom rank_K : Entity → ℕ
axiom rank_K_substrate : rank_K Ω = 0
axiom rank_K_grounding : ∀ e₁ e₂, grounds e₁ e₂ → rank_K e₂ < rank_K e₁
axiom rank_K_exists : ∀ e, ∃ n, rank_K e = n

noncomputable axiom rank_C : Entity → ℕ → ℕ
noncomputable axiom bfs_depth_C : Entity → ℕ → Finset Entity → ℕ
noncomputable def bfs_grounding_path (_e : Entity) (_S : Finset Entity) (_p : ℕ) : Option (List Entity) :=
  none
axiom rank_C_def : ∀ e p S,
  e ∈ S → rank_C e p = bfs_depth_C e p S
axiom universal_grounding : ∀ e,
  is_presentation e →
  ∃ path : List Entity,
    path.head? = some Ω ∧
    path.getLast? = some e ∧
    ∀ i : ℕ, ∀ h1 : i < path.length, ∀ h2 : i + 1 < path.length,
      grounds path[i] path[i+1]
section FinsetHelpers
variable {α : Type*} [DecidableEq α]

lemma card_lt_of_subset_ne {A B : Finset α}
    (hsub : A ⊆ B) (hne : A ≠ B) : A.card < B.card := by
  have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  simpa using Finset.card_lt_card hss

lemma card_lt_of_subset_exists_not_mem {A B : Finset α}
    (hsub : A ⊆ B) (h : ∃ x ∈ B, x ∉ A) : A.card < B.card := by
  rcases h with ⟨x, hxB, hxA⟩
  have hne : A ≠ B := by
    intro hEq
    have : x ∈ A := by simpa [hEq] using hxB
    exact hxA this
  exact card_lt_of_subset_ne hsub hne

lemma inter_subset_right (A B : Finset α) : A ∩ B ⊆ B := by
  intro x hx
  exact (Finset.mem_inter.mp hx).2

lemma inter_subset_left (A B : Finset α) : A ∩ B ⊆ A := by
  intro x hx
  exact (Finset.mem_inter.mp hx).1

end FinsetHelpers


section Examples
variable {Entity : Type} [DecidableEq Entity]


lemma visited_card_lt_of_room
  (visited S : Finset Entity)
  (hsub : visited ⊆ S)
  (hroom : ∃ x ∈ S, x ∉ visited) :
  visited.card < S.card :=
card_lt_of_subset_exists_not_mem hsub hroom


lemma inter_with_frontier_into_S
  (visited frontier S : Finset Entity)
  (hfrontier : frontier ⊆ S) :
  visited ∩ frontier ⊆ S :=
(inter_subset_right visited frontier).trans hfrontier

end Examples

end SubstrateTheory.Core
