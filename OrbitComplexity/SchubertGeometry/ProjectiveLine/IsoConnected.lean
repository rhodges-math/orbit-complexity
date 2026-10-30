import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected

/-! # Geometric fibres of a simple Schubert variety

The projective-line isomorphism identifies every geometric fibre with an integral
projective line. These fibres are therefore also connected.
-/

namespace SchubertGeometry
noncomputable section
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (i : G.rootBase.support)

/-- A simple Schubert variety has integral geometric fibres over its coefficient field. -/
instance simpleSchubert_geomIntegral :
    GeometricallyIntegral
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec := by
  let e := (Over.forget _).mapIso (simpleSchubertIso G i)
  have : GeometricallyIntegral (projectiveVariety K (ULift.{u} (Fin 2))).toSpec :=
    projectiveToSpec_geometricallyIntegral K _
  constructor
  intro F hF y Z fst snd h
  have h' : IsPullback (fst ≫ e.hom) snd
      (projectiveVariety K (ULift.{u} (Fin 2))).toSpec y :=
    h.of_iso (.refl _) e (.refl _) (.refl _)
      (by simp) (by simp)
      (by
        change (schubertVariety G
          (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec ≫ 𝟙 _ =
            (simpleSchubertIso G i).hom.left ≫
              (projectiveVariety K (ULift.{u} (Fin 2))).toSpec
        rw [Category.comp_id]
        exact (simpleSchubertIso G i).hom.w.symm)
      (by simp)
  exact GeometricallyIntegral.geometrically_isIntegral
    (f := (projectiveVariety K (ULift.{u} (Fin 2))).toSpec) y _ _ h'

/-- A simple Schubert variety has connected geometric fibres over its coefficient field. -/
instance simpleSchubert_geomConnected :
    GeometricallyConnected
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec := by
  constructor
  intro F hF y Z fst snd h
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral
    (f := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec)
    y fst snd h
  infer_instance

end
end SchubertGeometry
