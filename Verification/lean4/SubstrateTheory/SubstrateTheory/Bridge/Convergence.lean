import SubstrateTheory.Ideal.Complexity
import SubstrateTheory.Operational.Complexity
import SubstrateTheory.Core.Grounding
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SubstrateTheory.Bridge
open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational SubstrateTheory.Core
private noncomputable def two_to_neg (x : ℝ) : ℝ := Real.exp (-(x) * Real.log 2)

noncomputable def Z_ideal (S : Finset SubstrateTheory.Entity) : ℝ :=
  Finset.sum S (fun e => two_to_neg (K e))

noncomputable def Z_op (S : Finset SubstrateTheory.Entity) (p : ℕ) : ℝ :=
  Finset.sum S (fun e => two_to_neg (C e p))
noncomputable axiom Coh : List SubstrateTheory.Entity → List ℝ → ℝ
noncomputable axiom Coh_op : List SubstrateTheory.Entity → List ℝ → ℕ → ℝ
noncomputable axiom dCoh_dt : SubstrateTheory.Entity → ℝ → ℝ

def grounds_K (e₁ e₂ : SubstrateTheory.Entity) : Prop :=
  K_cond e₁ e₂ < K e₂ - K e₁ + c_grounding

def grounds_C (e₁ e₂ : SubstrateTheory.Entity) (p : ℕ) : Prop :=
  C_cond e₁ e₂ p < C e₂ p - C e₁ p + c_grounding

axiom BRIDGE1 :
  ∀ e ε, 0 < ε → is_presentation e →
  ∃ p₀ : ℕ, ∀ p ≥ p₀, |C e p - K e| < ε

axiom BRIDGE2 :
  ∀ (S : Finset SubstrateTheory.Entity) (ε : ℝ),
    0 < ε → (∀ e ∈ S, is_presentation e) →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ e ∈ S, |C e p - K e| < ε

axiom BRIDGE3 :
  ∀ (S : Finset SubstrateTheory.Entity) (ε : ℝ),
    0 < ε → (∀ e ∈ S, is_presentation e) → Z_ideal S > 0 →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, |Z_op S p - Z_ideal S| / Z_ideal S < ε

axiom BRIDGE4 :
  ∀ (S : Finset SubstrateTheory.Entity) (ε : ℝ) (e₁ e₂ : SubstrateTheory.Entity),
    0 < ε → e₁ ∈ S → e₂ ∈ S → is_presentation e₁ → is_presentation e₂ →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, (grounds_K e₁ e₂ ↔ grounds_C e₁ e₂ p)

axiom BRIDGE5 :
  ∀ (S : Finset SubstrateTheory.Entity) (e : SubstrateTheory.Entity),
    e ∈ S → is_presentation e →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, rank_C e p = rank_K e

axiom BRIDGE6 :
  ∀ (e : SubstrateTheory.Entity) (times : List ℝ) (ε : ℝ),
    0 < ε → is_temporal_presentation e →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ t ∈ times, |Coh_op [e] [t] p - Coh [e] [t]| < ε

axiom BRIDGE7 :
  ∀ (e₁ e₂ : SubstrateTheory.Entity) (ε : ℝ),
    0 < ε → is_presentation e₁ → is_presentation e₂ →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, |C_cond e₁ e₂ p - K_cond e₁ e₂| < ε

axiom BRIDGE7_joint :
  ∀ (es : List SubstrateTheory.Entity) (ε : ℝ),
    0 < ε → (∀ e ∈ es, is_presentation e) →
    ∃ p₀ : ℕ, ∀ p ≥ p₀, |C_joint es p - K_joint es| < ε

axiom BRIDGE8 :
  ∀ (e : SubstrateTheory.Entity) (times : List ℝ) (ε : ℝ),
    0 < ε → is_temporal_presentation e →
    ∃ p₀ δ, 0 < δ ∧
      ∀ p ≥ p₀, ∀ t ∈ times,
        |(Coh_op [e] [t + δ] p - Coh_op [e] [t] p) / δ - dCoh_dt e t| < ε

end SubstrateTheory.Bridge
