import OrbitComplexity.GroupActions.Actions.OrbitMap

/-! # Left translations and orbit morphisms

The regular action of a group variety gives its left translations. Associativity of an
algebraic action makes each orbit morphism commute with translation of the group and
translation of the acted-on variety.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H : Variety K) [GrpObj H.toOver]

/-- Left translation by a rational point is an isomorphism of the group variety. -/
def leftTranslation (h : H.points) : H.toOver ≅ H.toOver :=
  letI : ModObj H.toOver H.toOver := ModObj.regular _
  Variety.translationIso H H h

/-- Left translation on rational points is group multiplication. -/
theorem leftTranslation_points (h k : H.points) :
    Variety.mapPoints (leftTranslation H h).hom k = h * k := by
  let : ModObj H.toOver H.toOver := ModObj.regular _
  change Variety.mapPoints (Variety.translateMorphism H H h) k = h * k
  rw [Variety.mapPoints_translateMorphism]
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_mul]
  rfl

variable [IsAlgClosed K] (X : Variety K) [ModObj H.toOver X.toOver]

/-- The orbit morphism intertwines left translation with the action's translation. -/
theorem orbitMorphism_translation (x : X.points) (h : H.points) :
    (leftTranslation H h).hom ≫ Variety.orbitMorphism H X x =
      Variety.orbitMorphism H X x ≫ Variety.translateMorphism H X h := by
  apply Variety.mapPoints_injective
  funext k
  simp only [Variety.mapPoints_comp, leftTranslation_points, Variety.mapPoints_orbitMorphism,
    Variety.mapPoints_translateMorphism, mul_smul]

end

end GroupActions
