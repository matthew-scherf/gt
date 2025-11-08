import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Grounding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic 

namespace SubstrateTheory.Physics

open SubstrateTheory SubstrateTheory.Core

axiom particle_generation_structure :
  ∃ g1 g2 g3 : Entity,
  is_presentation g1 ∧ is_presentation g2 ∧ is_presentation g3 ∧
  rank_K g1 < rank_K g2 ∧ rank_K g2 < rank_K g3







noncomputable def generation_entities : Finset Entity :=
  let ⟨g1, g2, g3, h⟩ := particle_generation_structure
  {g1, g2, g3}





theorem generation_set_has_three_elements :
  (generation_entities).card = 3 := by
  
  simp [generation_entities]

  
  
  have ⟨g1, g2, g3, h_pres_g1, h_pres_g2, h_pres_g3, h_rank12, h_rank23⟩ :=
    particle_generation_structure

  
  
  
  
  

  
  have h_distinct : ∀ e1 e2, rank_K e1 < rank_K e2 → e1 ≠ e2 :=
    sorry 

  
  have h_g1_ne_g2 : g1 ≠ g2 := h_distinct g1 g2 h_rank12
  have h_g2_ne_g3 : g2 ≠ g3 := h_distinct g2 g3 h_rank23

  
  have h_g1_ne_g3 : g1 ≠ g3 := by
    apply h_distinct g1 g3
    
    linarith [h_rank12, h_rank23] 

  
  
  
  
  
  
  

  sorry 




axiom particle_generation_structure_v2 :
  ∃ g1 g2 g3 : Entity,
    g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 ∧
    is_presentation g1 ∧ is_presentation g2 ∧ is_presentation g3 ∧
    rank_K g1 < rank_K g2 ∧ rank_K g2 < rank_K g3


noncomputable def generation_entities_v2 : Finset Entity :=
  let ⟨g1, g2, g3, h⟩ := particle_generation_structure_v2
  {g1, g2, g3}

theorem generation_set_has_three_elements_v2 :
  (generation_entities_v2).card = 3 := by
  
  obtain ⟨g1, g2, g3, h_ne_12, h_ne_13, h_ne_23, h_pres⟩ :=
    particle_generation_structure_v2

  
  simp [generation_entities_v2]

  
  
  simp [Finset.card_insert_of_not_mem, h_ne_12, h_ne_13, h_ne_23]

end SubstrateTheory.Physics
