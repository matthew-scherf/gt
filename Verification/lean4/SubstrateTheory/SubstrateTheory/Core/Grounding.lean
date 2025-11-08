import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.Ideal.Complexity
import SubstrateTheory.Operational.Complexity
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SubstrateTheory.Core

open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational



noncomputable axiom rank_K : Entity → ℕ
axiom rank_K_substrate : rank_K Ω = 0
axiom rank_K_grounding : ∀ e₁ e₂, grounds e₁ e₂ → rank_K e₂ < rank_K e₁
axiom rank_K_exists : ∀ e, ∃ n, rank_K e = n
axiom groundsC_to_ideal (e₁ e₂ : Entity) (p : ℕ) :
  grounds_C e₁ e₂ p → grounds e₁ e₂
noncomputable axiom rank_C : Entity → ℕ → ℕ

def grounds_C (e₁ e₂ : Entity) (p : ℕ) : Prop :=
  C_cond e₁ e₂ p < C e₂ p - C e₁ p + c_grounding


open Classical in
noncomputable def grounds_graph (S : Finset Entity) (p : ℕ) : Finset (Entity × Entity) :=
  (S.product S).filter (fun (e₁, e₂) => grounds_C e₁ e₂ p)






noncomputable def grounding_graph_struct (S : Finset Entity) (p : ℕ) : SimpleGraph {e // e ∈ S} :=

  {
    Adj := fun (v₁ v₂ : {e // e ∈ S}) => grounds_C v₁.val v₂.val p,
    symm := by











      sorry
    loopless := by

      sorry
  }





noncomputable def parents_C (e : Entity) (S : Finset Entity) (p : ℕ) : Finset Entity :=
  S.filter (fun (parent : Entity) => grounds_C parent e p)





@[simp]
noncomputable def bfs_depth_C_aux (p : ℕ) (S : Finset Entity)
  (current_level : Finset Entity) (visited : Finset Entity) (depth : ℕ) : Finset (Entity × ℕ) :=
  if current_level.Empty then
    Finset.empty
  else
    let current_with_depth := current_level.image (fun e => (e, depth))
    let new_neighbors := (current_level.biUnion (fun e => parents_C e S p)).filter (fun e => e ∉ visited)
    let next_visited := visited ∪ new_neighbors
    current_with_depth ∪ (bfs_depth_C_aux p S new_neighbors next_visited (depth + 1))

noncomputable def bfs_depth_C (e : Entity) (p : ℕ) (S : Finset Entity) : ℕ :=





  let all_depths := bfs_depth_C_aux p S {Ω} {Ω} 0

  match (all_depths.filter (fun (x, d) => x = e)).max by
    | some (e, depth) => depth
    | none => 0







noncomputable def bfs_grounding_path (e : Entity) (S : Finset Entity) (p : ℕ) : Option (List Entity) :=


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

axiom grounding_transitive : ∀ e₁ e₂ e₃,
  grounds e₁ e₂ → grounds e₂ e₃ → grounds e₁ e₃

axiom grounding_acyclic : ∀ e,
  ¬grounds e e

end SubstrateTheory.Core
