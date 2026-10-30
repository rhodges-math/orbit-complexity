import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteAffineRefinements
import OrbitComplexity.SchubertGeometry.BSDH.Construction

/-!
# Finite BSDH flag atlases

Finite affine patches retain their endpoint lifts to translated flag charts.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry

universe u

/-- Each iterated simple-Schubert scheme has a finite affine cover whose endpoint
maps factor through specified translated unipotent flag charts. -/
theorem bsdh_finite_flag_cover {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support) :
    ∃ 𝒰 : (bsdhScheme G word).OpenCover.{u}, Finite 𝒰.I₀ ∧
      (∀ i, IsAffine (𝒰.X i)) ∧
      ∃ (g : 𝒰.I₀ → G.points)
        (lift : ∀ i, 𝒰.X i ⟶ (GroupActions.oppositeUnipotentVariety G).scheme),
        ∀ i, lift i ≫ flagSchemeChart G (g i) = 𝒰.f i ≫ bsdhMap G word := by
  have : CompactSpace (bsdhScheme G word) :=
    QuasiCompact.compactSpace_of_compactSpace (bsdhToSpec G word)
  let 𝒱 := (flagSchemeCover G).pullback₁ (bsdhMap G word)
  obtain ⟨𝒰, hfinite, haffine, ⟨r⟩⟩ :=
    FrobeniusSplitting.exists_affine_cover_refinement 𝒱
  refine ⟨𝒰, hfinite, haffine, (fun i ↦ r.s₀ i),
    (fun i ↦ r.h₀ i ≫ (flagSchemeCover G).pullbackHom (bsdhMap G word) (r.s₀ i)), ?_⟩
  intro i
  have hp : (flagSchemeCover G).pullbackHom (bsdhMap G word) (r.s₀ i) ≫
      flagSchemeChart G (r.s₀ i) = 𝒱.f (r.s₀ i) ≫ bsdhMap G word :=
    (flagSchemeCover G).pullbackHom_map (bsdhMap G word) (r.s₀ i)
  have hr : r.h₀ i ≫ 𝒱.f (r.s₀ i) = 𝒰.f i := r.w₀ i
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k : 𝒱.X (r.s₀ i) ⟶ flagScheme G ↦ r.h₀ i ≫ k) hp).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : 𝒰.X i ⟶ bsdhScheme G word ↦ k ≫ bsdhMap G word) hr)))

end SchubertGeometry
