import OrbitComplexity.FrobeniusSplitting.Cartier.AffineBasis

/-! # Residue coordinates on sections of the affine Frobenius module -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.AffineCartier

variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p]

private abbrev affineLine := Spec (.of (Polynomial C))
private abbrev residueIndex := ULift.{u} (Fin p)

private def sourceModule : (affineLine C).Modules :=
  frobeniusRestriction C p
    (Spec.map (CommRingCat.ofHom (Polynomial.C : C →+* Polynomial C)))
    (SheafOfModules.unit (affineLine C).ringCatSheaf)

private def basisIso :
    (SheafOfModules.free (R := (affineLine C).ringCatSheaf) (residueIndex p) :
      (affineLine C).Modules) ≅ sourceModule C p := affineFrobeniusBasisIso C p

/-- On any open, Frobenius sections have finite residue coordinates. -/
def affineFrobeniusSectionIso (U : (affineLine C).Opens) :
    ModuleCat.of Γ(affineLine C, U) (residueIndex p →₀ Γ(affineLine C, U)) ≅
      (sourceModule C p).val.obj (op U) :=
  finiteFreeSectionsIso (affineLine C) U (residueIndex p) ≪≫
    (SheafOfModules.evaluation (affineLine C).ringCatSheaf (op U)).mapIso (basisIso C p)

/-- A single residue coordinate multiplies the monomial by the pth power of its coefficient. -/
theorem affineFrobeniusSectionIso_single (U : (affineLine C).Opens) (i : Fin p)
    (r : Γ(affineLine C, U)) :
    (show Γ(affineLine C, U) from (affineFrobeniusSectionIso C p U).hom.hom
      (Finsupp.single (ULift.up i) r)) =
        r ^ p * (((Scheme.ΓSpecIso (.of (Polynomial C))).inv ≫
          (affineLine C).presheaf.map U.leTop.op)
          ((Polynomial.X : Polynomial C) ^ (i : ℕ))) := by
  let t := SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf)
    (I := residueIndex p) (ULift.up i) ≫ (basisIso C p).hom
  have hs := congrArg
    (fun m : (SheafOfModules.free (R := (affineLine C).ringCatSheaf)
        (residueIndex p)).val.obj (op U) =>
      (show Γ(affineLine C, U) from ((basisIso C p).hom.val.app (op U)).hom m))
    (finiteFreeSectionsIso_single (affineLine C) U (residueIndex p) (ULift.up i) r)
  change (show Γ(affineLine C, U) from
      (affineFrobeniusSectionIso C p U).hom.hom (Finsupp.single (ULift.up i) r)) =
    (show Γ(affineLine C, U) from (t.val.app (op U)).hom r) at hs
  have hlin : (show Γ(affineLine C, U) from (t.val.app (op U)).hom r) =
      r ^ p * (show Γ(affineLine C, U) from
        (t.val.app (op U)).hom (1 : Γ(affineLine C, U))) := by
    have h := (t.val.app (op U)).hom.map_smul r (1 : Γ(affineLine C, U))
    change (show Γ(affineLine C, U) from (t.val.app (op U)).hom (r * (1 : Γ(affineLine C, U)))) =
      r ^ p * (show Γ(affineLine C, U) from
        (t.val.app (op U)).hom (1 : Γ(affineLine C, U))) at h
    exact (congrArg (fun m : Γ(affineLine C, U) =>
      (show Γ(affineLine C, U) from (t.val.app (op U)).hom m)) (mul_one r)).symm.trans h
  have hg : (show Γ(affineLine C, U) from
      (t.val.app (op U)).hom (1 : Γ(affineLine C, U))) =
    ((Scheme.ΓSpecIso (.of (Polynomial C))).inv ≫
      (affineLine C).presheaf.map U.leTop.op) ((Polynomial.X : Polynomial C) ^ (i : ℕ)) :=
    affineFrobeniusBasisIso_generator C p U i
  exact hs.trans (hlin.trans (congrArg (fun m : Γ(affineLine C, U) => r ^ p * m) hg))

end FrobeniusSplitting.AffineCartier
