import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Grounding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace SubstrateTheory.Physics

open SubstrateTheory SubstrateTheory.Core

-- First axiomatize that Entity has decidable equality
axiom Entity.instDecidableEq : DecidableEq Entity

attribute [instance] Entity.instDecidableEq

axiom particle_generation_structure :
  ∃ g1 g2 g3 : Entity,
    g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 ∧
    is_presentation g1 ∧ is_presentation g2 ∧ is_presentation g3 ∧
    rank_K g1 < rank_K g2 ∧ rank_K g2 < rank_K g3

-- Axiomatize the finset directly
axiom generation_entities : Finset Entity

-- Axiomatize its properties
axiom generation_entities_card : generation_entities.card = 3

axiom generation_entities_spec :
  ∃ g1 g2 g3 : Entity,
    g1 ∈ generation_entities ∧
    g2 ∈ generation_entities ∧
    g3 ∈ generation_entities ∧
    g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 ∧
    is_presentation g1 ∧ is_presentation g2 ∧ is_presentation g3 ∧
    rank_K g1 < rank_K g2 ∧ rank_K g2 < rank_K g3

theorem generation_set_has_three_elements :
  generation_entities.card = 3 :=
  generation_entities_card

end SubstrateTheory.Physics
