import OrbitComplexity.GroupActions.Rosenlicht.ActionFields
import OrbitComplexity.GroupActions.Rosenlicht.GenericOrbit
import OrbitComplexity.GroupActions.Rosenlicht.RationalSpecialization
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections

/-!
# Rational relations of the algebraic action

The action and the second projection pull rational functions back to the
group-variety product. A polynomial relation between those pullbacks specializes
to a relation at every rational point translation.

## Main definitions

* `Variety.actionRelationMap`: evaluation using the action and the second projection.

## Main results

* `Variety.actionRelation_ideal_le`: algebraic action relations are point orbit relations.
* `Variety.actionRelation_ideal_eq`: the two ideals of generic action relations agree.
* `Variety.genericOrbitIdeal_isPrime`: generic orbit relation ideals are prime.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

private instance over_irreducible : IrreducibleSpace X.toOver.left :=
  inferInstanceAs (IrreducibleSpace X.scheme)

private instance projection_surjective : Surjective (snd H.toOver X.toOver).left := by
  let s : X.toOver ⟶ H.toOver ⊗ X.toOver :=
    lift (toUnit X.toOver ≫ H.pointsEquivOverHom 1) (𝟙 X.toOver)
  have hs : s ≫ snd H.toOver X.toOver = 𝟙 X.toOver := by simp [s]
  constructor
  intro x
  refine ⟨s.left x, ?_⟩
  exact congrArg (fun f : X.scheme ⟶ X.scheme ↦ f x) (congrArg Over.Hom.left hs)

/-- Polynomial evaluation using pullback of coefficients by the second projection
and pullback of variables by the algebraic action. -/
def actionRelationMap {ι : Type v} (x : ι → X.scheme.functionField) :
    letI := product_integral H X
    MvPolynomial ι X.scheme.functionField →+* (H.toOver ⊗ X.toOver).left.functionField :=
  letI := product_integral H X
  MvPolynomial.eval₂Hom
    (functionFieldMap ((snd H.toOver X.toOver).left :
      (H.toOver ⊗ X.toOver).left ⟶ X.scheme))
    (fun i ↦ functionFieldMap ((ModObj.smul (M := H.toOver) (X := X.toOver)).left :
      (H.toOver ⊗ X.toOver).left ⟶ X.scheme) (x i))

/-- Every relation of the algebraic action specializes to a relation of every
rational point translate. -/
theorem actionRelation_ideal_le {ι : Type v} (x : ι → X.scheme.functionField) :
    letI := product_integral H X
    RingHom.ker (actionRelationMap H X x) ≤ genericOrbitIdeal H X x := by
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := product_integral H X
  let _ := functionFieldAction (schemeTranslationHom H X)
  intro q hq
  change q ∈ orbitIdeal (G := H.points) x
  rw [mem_orbitIdeal_iff]
  intro h
  let sOver : X.toOver ⟶ H.toOver ⊗ X.toOver :=
    lift (toUnit X.toOver ≫ H.pointsEquivOverHom h⁻¹) (𝟙 X.toOver)
  let s : X.scheme ⟶ (H.toOver ⊗ X.toOver).left := sOver.left
  have hp : s ≫ (snd H.toOver X.toOver).left = 𝟙 X.scheme := by
    exact congrArg Over.Hom.left (show sOver ≫ snd H.toOver X.toOver = 𝟙 X.toOver by
      simp [sOver])
  have ha : s ≫ (ModObj.smul (M := H.toOver) (X := X.toOver)).left =
      (translateMorphism H X h⁻¹).left := rfl
  have : IsDominant (s ≫ (snd H.toOver X.toOver).left) := by
    rw [hp]
    constructor
    exact denseRange_id
  have : IsIso (translateMorphism H X h⁻¹).left := by
    change IsIso ((Over.forget (Spec (.of K))).map (translationIso H X h⁻¹).hom)
    infer_instance
  have : IsDominant (s ≫ (ModObj.smul (M := H.toOver) (X := X.toOver)).left) := by
    rw [ha]
    infer_instance
  have hs := functionField_relation_specialize
    ((snd H.toOver X.toOver).left : (H.toOver ⊗ X.toOver).left ⟶ X.scheme)
    ((ModObj.smul (M := H.toOver) (X := X.toOver)).left :
      (H.toOver ⊗ X.toOver).left ⟶ X.scheme) s x q
    (show actionRelationMap H X x q = 0 from hq)
  simp only [hp, ha, functionFieldMap_id] at hs
  exact hs

/-- The polynomial relations of the algebraic action are exactly the relations
of all rational point translations. -/
theorem actionRelation_ideal_eq {ι : Type v} (x : ι → X.scheme.functionField) :
    letI := product_integral H X
    RingHom.ker (actionRelationMap H X x) = genericOrbitIdeal H X x := by
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := product_integral H X
  let _ := functionFieldAction (schemeTranslationHom H X)
  apply le_antisymm (actionRelation_ideal_le H X x)
  intro q hq
  change q ∈ orbitIdeal (G := H.points) x at hq
  rw [mem_orbitIdeal_iff] at hq
  let p : (H.toOver ⊗ X.toOver).left ⟶ X.scheme := (snd H.toOver X.toOver).left
  let a : (H.toOver ⊗ X.toOver).left ⟶ X.scheme :=
    (ModObj.smul (M := H.toOver) (X := X.toOver)).left
  let s (h : H.points) : X.scheme ⟶ (H.toOver ⊗ X.toOver).left :=
    (pointSection H X h).left
  have hp (h : H.points) : s h ≫ p = 𝟙 X.scheme :=
    congrArg Over.Hom.left (pointSection_snd H X h)
  have ha (h : H.points) : s h ≫ a = (translateMorphism H X h).left := rfl
  let _ : ∀ h, IsDominant (s h ≫ p) := fun h ↦ by
    rw [hp]
    constructor
    exact denseRange_id
  let _ : ∀ h, IsDominant (s h ≫ a) := fun h ↦ by
    have : IsIso (translateMorphism H X h).left := by
      change IsIso ((Over.forget (Spec (.of K))).map (translationIso H X h).hom)
      infer_instance
    rw [ha]
    infer_instance
  change MvPolynomial.eval₂Hom (functionFieldMap p)
    (fun i ↦ functionFieldMap a (x i)) q = 0
  apply (functionField_relation_iff p a s (pointSection_generic_dense H X) x q).mpr
  intro h
  have hinv : ((schemeTranslationHom H X) h⁻¹).inv =
      (translateMorphism H X h).left := by
    change (translateMorphism H X (h⁻¹)⁻¹).left = _
    rw [inv_inv]
  have ho := hq h⁻¹
  change MvPolynomial.eval₂Hom (RingHom.id X.scheme.functionField)
    (fun i ↦ functionFieldMap ((schemeTranslationHom H X) h⁻¹).inv (x i)) q = 0 at ho
  simpa only [hp h, ha h, functionFieldMap_id, hinv] using ho

/-- The generic orbit relations of an irreducible algebraic group form a prime ideal. -/
theorem genericOrbitIdeal_isPrime {ι : Type v} (x : ι → X.scheme.functionField) :
    (genericOrbitIdeal H X x).IsPrime := by
  have := product_integral H X
  rw [← actionRelation_ideal_eq H X x]
  exact RingHom.ker_isPrime _

end

end GroupActions.Variety
