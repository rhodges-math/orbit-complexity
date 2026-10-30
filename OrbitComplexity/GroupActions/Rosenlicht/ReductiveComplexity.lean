import OrbitComplexity.GroupActions.Rosenlicht.BirationalInvariants
import OrbitComplexity.GroupActions.Complexity.Basic
import OrbitComplexity.GroupActions.Actions.Restriction

/-!
# Birational invariance of reductive complexity

Equivariance for an algebraic group restricts to every subgroup. In particular,
an equivariant birational rational map preserves the minimum codimension of
orbits of the chosen Borel subgroup, hence preserves complexity.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K]

private lemma translate_restrict {H G : Variety K} [GrpObj H.toOver] [GrpObj G.toOver]
    (i : H.toOver ⟶ G.toOver) [IsMonHom i] (X : Variety K)
    [ModObj G.toOver X.toOver] (h : H.points) :
    letI := Mod.scalarRestriction i X.toOver
    Variety.translateMorphism H X h =
      Variety.translateMorphism G X (Variety.mapPoints i h) := by
  let := Mod.scalarRestriction i X.toOver
  change lift (toUnit X.toOver ≫ H.pointsEquivOverHom h) (𝟙 X.toOver) ≫
      ((i ▷ X.toOver) ≫ ModObj.smul (M := G.toOver) (X := X.toOver)) =
    lift (toUnit X.toOver ≫ G.pointsEquivOverHom (Variety.mapPoints i h))
      (𝟙 X.toOver) ≫ ModObj.smul (M := G.toOver) (X := X.toOver)
  rw [← Category.assoc, lift_whiskerRight]
  rfl

private lemma schemeTranslation_restrict {H G : Variety K}
    [GrpObj H.toOver] [GrpObj G.toOver] (i : H.toOver ⟶ G.toOver) [IsMonHom i]
    (X : Variety K) [ModObj G.toOver X.toOver] (h : H.points) :
    letI := Mod.scalarRestriction i X.toOver
    Variety.schemeTranslationHom H X h =
      Variety.schemeTranslationHom G X (Variety.mapPointsHom i h) := by
  let := Mod.scalarRestriction i X.toOver
  apply Iso.ext
  exact congrArg Over.Hom.left (translate_restrict i X h)

variable [IsAlgClosed K] (G : ReductiveGroups.ReductiveGroupData K) (X Y : Variety K)
variable [ModObj (reductiveVariety G).toOver X.toOver]
variable [ModObj (reductiveVariety G).toOver Y.toOver]
variable [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme]

/-- An equivariant birational rational map preserves the complexity of an
irreducible variety under a reductive algebraic group. -/
theorem complexity_eq_of_birational (f : X.scheme.PartialIso Y.scheme)
    (hf : f.IsOver X.toSpec Y.toSpec)
    (heq : RationalEquivariant (Variety.schemeTranslationHom (reductiveVariety G) X)
      (Variety.schemeTranslationHom (reductiveVariety G) Y) f.toPartialMap) :
    complexity G X = complexity G Y := by
  let := Mod.scalarRestriction (borelInclusion G) X.toOver
  let := Mod.scalarRestriction (borelInclusion G) Y.toOver
  apply Variety.minOrbitCodim_eq_of_birational (borelVariety G) X Y f hf
  intro h
  rw [schemeTranslation_restrict (borelInclusion G) X h,
    schemeTranslation_restrict (borelInclusion G) Y h]
  exact heq (Variety.mapPointsHom (borelInclusion G) h)

end

end GroupActions
