import OrbitComplexity.SchubertGeometry.Parabolics.SchubertProjection
import OrbitComplexity.SchubertGeometry.Parabolics.CellClosure
import OrbitComplexity.SchubertGeometry.Parabolics.CellIso
import OrbitComplexity.SchubertGeometry.Levi.CellComplexity
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Birational Schubert projections

For a minimum right representative, the dense open cell isomorphism agrees with
the proper projection of Schubert varieties.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem cellMap_comp (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (partialCellIso G J w hw).hom ≫ partialCellInClosure G J w =
      schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w) ≫
        partialSchubertProjection G J w := by
  have : Mono (partialSchubertInclusion G J w) := Over.mono_of_mono_left _
  apply (cancel_mono (partialSchubertInclusion G J w)).mp
  rw [Category.assoc, partialCellInClosure_comp, partialCellIso_hom,
    partialCellProjection_comp, Category.assoc, partialSchubertProjection_comp,
    ← Category.assoc, schubertCellOfLE_comp]

private theorem schubert_birational (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    ∃ p : (schubertVariety G w).scheme.PartialIso (partialSchubertVariety G J w).scheme,
      p.IsOver (schubertVariety G w).toSpec (partialSchubertVariety G J w).toSpec ∧
      p.source.ι ≫ (partialSchubertProjection G J w).left = p.iso.hom ≫ p.target.ι := by
  let iw : (schubertCell G w).scheme ⟶ (schubertVariety G w).scheme :=
    (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w)).left
  let ij : (partialSchubertCell G J w).scheme ⟶
      (partialSchubertVariety G J w).scheme := (partialCellInClosure G J w).left
  let ec : (schubertCell G w).scheme ≅ (partialSchubertCell G J w).scheme :=
    (Over.forget _).mapIso (partialCellIso G J w hw)
  have hc : ec.hom ≫ ij = iw ≫ (partialSchubertProjection G J w).left :=
    congrArg Over.Hom.left (cellMap_comp G J w hw)
  let p : (schubertVariety G w).scheme.PartialIso (partialSchubertVariety G J w).scheme :=
    { source := iw.opensRange
      dense_source := iw.denseRange
      target := ij.opensRange
      dense_target := ij.denseRange
      iso := iw.isoOpensRange.symm ≪≫ ec ≪≫ ij.isoOpensRange }
  have hp : p.iso.hom ≫ p.target.ι =
      p.source.ι ≫ (partialSchubertProjection G J w).left := by
    dsimp only [p, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    rw [hc, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  refine ⟨p, ?_, hp.symm⟩
  change p.iso.hom ≫ p.target.ι ≫ (partialSchubertVariety G J w).toSpec =
    p.source.ι ≫ (schubertVariety G w).toSpec
  have hf : (partialSchubertProjection G J w).left ≫
      (partialSchubertVariety G J w).toSpec = (schubertVariety G w).toSpec :=
    (partialSchubertProjection G J w).w
  rw [← Category.assoc, hp, Category.assoc, hf]

/-- The Schubert projection is proper and surjective, and minimum representatives give
a compatible birational map over the base field. -/
theorem partialSchubertProjection_properties (J : Set G.rootBase.support)
    (w : G.weylGroup) :
    (partialSchubertProjection G J w ≫ partialSchubertInclusion G J w =
      schubertInclusion G w ≫ partialFlagMorphism G J) ∧
    Surjective (partialSchubertProjection G J w).left ∧
    IsProper (partialSchubertProjection G J w).left ∧
    (IsMinimalRightParabolic G.rootBase J w →
      ∃ p : (schubertVariety G w).scheme.PartialIso (partialSchubertVariety G J w).scheme,
        p.IsOver (schubertVariety G w).toSpec (partialSchubertVariety G J w).toSpec ∧
        p.source.ι ≫ (partialSchubertProjection G J w).left = p.iso.hom ≫ p.target.ι) :=
  ⟨partialSchubertProjection_comp G J w, inferInstance, inferInstance,
    schubert_birational G J w⟩

end SchubertGeometry
