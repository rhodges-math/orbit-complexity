import OrbitComplexity.GroupActions.Rosenlicht.RelationFields
import OrbitComplexity.GroupActions.Rosenlicht.RelationKernels
import OrbitComplexity.GroupActions.Rosenlicht.InvariantMaps

/-!
# Invariant functions as an equalizer

A rational function is invariant precisely when its pullbacks through the two
projections of the orbit relation closure agree. The polynomial relation with
one variable identifies this equality with invariance under every translation.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- Invariant rational functions equalize the two orbit relation projections. -/
theorem mem_invariantField_iff_relation (f : X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    f ∈ invariantField H X ↔ relationFirstFieldMap H X f = relationSecondFieldMap H X f := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let _ : Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
    (relationFirstFieldMap H X).toAlgebra
  let _ := functionFieldAction (schemeTranslationHom H X)
  let p : MvPolynomial Unit X.scheme.functionField := MvPolynomial.X () - MvPolynomial.C f
  have hm : p ∈ genericOrbitIdeal H X (fun _ : Unit ↦ f) ↔ f ∈ invariantField H X := by
    change p ∈ orbitIdeal (G := H.points) (fun _ : Unit ↦ f) ↔
      ∀ h : H.points, h • f = f
    simp only [mem_orbitIdeal_iff, p, map_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_eq_zero]
  have hk : p ∈ genericOrbitIdeal H X (fun _ : Unit ↦ f) ↔
      relationSecondFieldMap H X f = relationFirstFieldMap H X f := by
    rw [← relationField_ker_eq H X (fun _ : Unit ↦ f)]
    change (MvPolynomial.aeval (fun _ : Unit ↦ relationSecondFieldMap H X f) :
      MvPolynomial Unit X.scheme.functionField →ₐ[X.scheme.functionField]
        (orbitRelationVariety H X).scheme.functionField) p = 0 ↔ _
    simp only [p, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero]
    rfl
  exact hm.symm.trans (hk.trans eq_comm)

/-- The invariant rational map agrees on the two generic relation projections. -/
theorem invariantMap_relation_field :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    Spec.map (CommRingCat.ofHom (relationFirstFieldMap H X)) ≫
        (invariantMap H X).fromFunctionField =
      Spec.map (CommRingCat.ofHom (relationSecondFieldMap H X)) ≫
        (invariantMap H X).fromFunctionField := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  let E := invariantField H X
  have hq : (invariantMap H X).fromFunctionField =
      Spec.map (CommRingCat.ofHom (E.val.comp (fieldModelAlgebra K E).val).toRingHom) :=
    intermediateRationalMap_field K E
  rw [hq]
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact (mem_invariantField_iff_relation H X a.val.val).mp a.val.property

end

end GroupActions.Variety
