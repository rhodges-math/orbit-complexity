import OrbitComplexity.GroupActions.Rosenlicht.RationalEquivariance
import OrbitComplexity.GroupActions.Actions.OrbitMap

/-! # Equivariance of a compatible birational restriction

A partial isomorphism agreeing with an equivariant regular morphism represents its
equivariant rational map. The chosen dense opens need not be invariant.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
noncomputable section
universe u v

namespace GroupActions

private theorem rational_of_regular {X Y : Scheme.{u}} [IsIntegral X]
    {M : Type v} [Monoid M] (ρ : M →* Aut X) (σ : M →* Aut Y)
    (F : X ⟶ Y) (p : X.PartialMap Y)
    (hp : p.hom = p.domain.ι ≫ F)
    (hF : ∀ m, (ρ m).inv ≫ F = F ≫ (σ m).inv) :
    RationalEquivariant ρ σ p := by
  have hgeneric : p.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ F := by
    change p.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ p.hom = _
    rw [hp, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  intro m
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMapPrecompose_generic]
  change Spec.map (CommRingCat.ofHom (functionFieldMap (ρ m).inv)) ≫
      p.fromFunctionField = p.fromFunctionField ≫ (σ m).inv
  rw [hgeneric, ← Category.assoc, functionFieldMap_genericPoint, Category.assoc, hF]
  simp only [Category.assoc]

namespace Variety

private theorem translation_commutes {K : Type u} [Field K]
    (H X Y : GroupActions.Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (F : X.toOver ⟶ Y.toOver) [IsModHom H.toOver F] (h : H.points) :
    translateMorphism H X h ≫ F = F ≫ translateMorphism H Y h := by
  unfold translateMorphism
  rw [IsModHom.map_smul, ModObj.comp_smul]
  simp only [Category.id_comp, Category.comp_id, comp_toUnit_assoc]

/-- A birational restriction of an equivariant morphism is rationally equivariant. -/
theorem partialIso_rationalEquivariant {K : Type u} [Field K]
    (H X Y : GroupActions.Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    [IrreducibleSpace X.scheme]
    (F : X.toOver ⟶ Y.toOver) [IsModHom H.toOver F]
    (p : X.scheme.PartialIso Y.scheme)
    (hp : p.iso.hom ≫ p.target.ι = p.source.ι ≫ F.left) :
    RationalEquivariant (schemeTranslationHom H X) (schemeTranslationHom H Y)
      p.toPartialMap := by
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  refine rational_of_regular (X := X.scheme) (Y := Y.scheme) _ _ F.left p.toPartialMap hp ?_
  intro h
  change (translateMorphism H X h⁻¹).left ≫ F.left =
    F.left ≫ (translateMorphism H Y h⁻¹).left
  exact congrArg (fun f : X.toOver ⟶ Y.toOver => f.left)
    (translation_commutes H X Y F h⁻¹)

end Variety
end GroupActions
