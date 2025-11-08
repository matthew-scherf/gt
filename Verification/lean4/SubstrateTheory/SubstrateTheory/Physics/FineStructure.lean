import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Ideal.Complexity
import Mathlib.Data.Real.Basic

namespace SubstrateTheory.Physics

open SubstrateTheory SubstrateTheory.Ideal

axiom fine_structure_derivation :
  is_presentation P_α →
  ∃ k : ℝ, α = k / (K P_EM)

axiom gravitational_constant_derivation :
  is_presentation P_G →
  ∃ k : ℝ, G = k / (K P_GR)

end SubstrateTheory.Physics
