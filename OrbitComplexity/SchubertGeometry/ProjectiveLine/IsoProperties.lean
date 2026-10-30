import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing

/-! # Properness of a simple Schubert variety

The isomorphism with the polynomial projective line preserves the structure map
to the coefficient field and transports its properness.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (i : G.rootBase.support)
/-- A simple Schubert variety is proper over its coefficient field. -/
instance simpleSchubert_isProper :
    IsProper (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec := by
  have : IsIso (simpleSchubertIso G i).hom.left :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (simpleSchubertIso G i)).hom))
  have : IsProper (projectiveVariety K (ULift.{u} (Fin 2))).toSpec :=
    projectiveToSpec_isProper K _
  have he : (simpleSchubertIso G i).hom.left ≫
      (projectiveVariety K (ULift.{u} (Fin 2))).toSpec =
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec :=
    (simpleSchubertIso G i).hom.w
  rw [← he]
  infer_instance
end SchubertGeometry
