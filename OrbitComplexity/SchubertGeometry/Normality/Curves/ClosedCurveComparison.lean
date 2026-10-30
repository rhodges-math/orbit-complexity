import OrbitComplexity.FrobeniusSplitting.Normality.Products.PairedScalarComparison
import OrbitComplexity.SchubertGeometry.Parabolics.CurveIntersection
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange

/-! # The closed simple-curve intersection on the retained flag model -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting

namespace SchubertGeometry

universe u

/-- The original simple Schubert curve uses the fixed coefficient map of P1. -/
def simpleCurveCoefficientMap
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K) (i : G.rootBase.support) :=
  (simpleSchubertIso G i).hom.left ≫
    projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap S K)

private theorem simpleCurveCoefficient_cartesian
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K) (i : G.rootBase.support) :
    IsPullback (simpleCurveCoefficientMap S G i)
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
  let X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let a := projectiveToSpec S (ULift.{u} (Fin 2))
  let eX : X.scheme ≅ projectiveScheme K (ULift.{u} (Fin 2)) :=
    (Over.forget (Spec (.of K))).mapIso (simpleSchubertIso G i)
  let e : X.scheme ≅ pullback κ a := eX ≪≫
    projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap S K)
  have hfst : e.hom ≫ pullback.fst κ a = X.toSpec :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => eX.hom ≫ q)
        (projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap S K))).trans
          (simpleSchubertIso G i).hom.w)
  have hsnd : e.hom ≫ pullback.snd κ a = simpleCurveCoefficientMap S G i :=
    (Category.assoc _ _ _).trans
      (congrArg (fun q => eX.hom ≫ q)
        (projectiveBaseChange_snd (ULift.{u} (Fin 2)) (algebraMap S K)))
  have hw : X.toSpec ≫ κ = simpleCurveCoefficientMap S G i ≫ a := by
    calc
      X.toSpec ≫ κ = (e.hom ≫ pullback.fst κ a) ≫ κ :=
        congrArg (fun q => q ≫ κ) hfst.symm
      _ = e.hom ≫ (pullback.fst κ a ≫ κ) := Category.assoc _ _ _
      _ = e.hom ≫ (pullback.snd κ a ≫ a) :=
        congrArg (fun q => e.hom ≫ q) (pullback.condition (f := κ) (g := a))
      _ = (e.hom ≫ pullback.snd κ a) ≫ a := (Category.assoc _ _ _).symm
      _ = simpleCurveCoefficientMap S G i ≫ a := congrArg (fun q => q ≫ a) hsnd
  exact (IsPullback.of_iso_pullback ⟨hw⟩ e hfst hsnd).flip


end SchubertGeometry
