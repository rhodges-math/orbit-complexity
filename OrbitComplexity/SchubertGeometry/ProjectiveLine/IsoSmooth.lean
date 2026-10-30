import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsSmooth

/-! # Smoothness of a simple Schubert variety

The isomorphism with the polynomial projective line transports smoothness over the
coefficient field. The structure-map equality comes from the isomorphism over the base.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (i : G.rootBase.support)

/-- A simple Schubert variety is smooth over its coefficient field. -/
instance simpleSchubert_smooth :
    Smooth (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec := by
  have : IsIso (simpleSchubertIso G i).hom.left :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (simpleSchubertIso G i)).hom))
  have : Smooth (projectiveVariety K (ULift.{u} (Fin 2))).toSpec :=
    projectiveToSpec_smooth K _
  have he : (simpleSchubertIso G i).hom.left ≫
      (projectiveVariety K (ULift.{u} (Fin 2))).toSpec =
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec :=
    (simpleSchubertIso G i).hom.w
  rw [← he]
  infer_instance
end SchubertGeometry
