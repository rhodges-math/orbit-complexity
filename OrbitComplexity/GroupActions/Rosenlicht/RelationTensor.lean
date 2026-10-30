import OrbitComplexity.GroupActions.Rosenlicht.RelationEqualizer
import OrbitComplexity.GroupActions.Rosenlicht.InvariantDescent
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Tensor embedding of the orbit relation fields
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The two projections of the orbit relation closure give a tensor map over
the invariant rational-function field. -/
def relationTensorMap :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    X.scheme.functionField ⊗[invariantField H X] X.scheme.functionField →+*
      (orbitRelationVariety H X).scheme.functionField := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let F := X.scheme.functionField
  let E := invariantField H X
  let L := (orbitRelationVariety H X).scheme.functionField
  let : Algebra E L := ((relationFirstFieldMap H X).comp E.subtype).toAlgebra
  let i : F →ₐ[E] L :=
    { __ := relationFirstFieldMap H X, commutes' := fun _ ↦ rfl }
  let j : F →ₐ[E] L :=
    { __ := relationSecondFieldMap H X
      commutes' := fun e ↦ ((mem_invariantField_iff_relation H X e.val).mp e.property).symm }
  exact (Algebra.TensorProduct.lift i j (fun _ _ ↦ Commute.all _ _)).toRingHom

end

end GroupActions.Variety

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

omit [IsAlgClosed K] [IrreducibleSpace H.scheme] in
private lemma relationTensor_polynomial {ι : Type u} [Finite ι]
    (x : ι → X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    genericOrbitIdeal H X x ≤ RingHom.ker (MvPolynomial.eval₂Hom
      (Algebra.TensorProduct.includeLeft : X.scheme.functionField →ₐ[invariantField H X]
        X.scheme.functionField ⊗[invariantField H X] X.scheme.functionField).toRingHom
      (fun i ↦ Algebra.TensorProduct.includeRight (x i))) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ := functionFieldAction (schemeTranslationHom H X)
  have : SMulCommClass H.points K X.scheme.functionField :=
    functionFieldAction_smulComm K (translationHom H X)
  let F := X.scheme.functionField
  let E := invariantField H X
  let θ := MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F).toRingHom
    (fun i ↦ Algebra.TensorProduct.includeRight (x i))
  obtain ⟨s, hs, hc⟩ := exists_invariant_relations H X x
  change orbitIdeal (G := H.points) x ≤ RingHom.ker θ
  rw [← orbitIdeal_map_comap_eq E x (s : Set (MvPolynomial ι F)) hs hc]
  apply Ideal.map_le_iff_le_comap.mpr
  rw [orbitIdeal_comap_eq E le_rfl x]
  intro p hp
  change θ (MvPolynomial.map E.subtype p) = 0
  have he : θ (MvPolynomial.map E.subtype p) =
      Algebra.TensorProduct.includeRight (MvPolynomial.aeval x p) := by
    change MvPolynomial.eval₂Hom
      (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F).toRingHom
      (fun i ↦ Algebra.TensorProduct.includeRight (x i)) (MvPolynomial.map E.subtype p) =
      (Algebra.TensorProduct.includeRight : F →ₐ[E] F ⊗[E] F).toRingHom
        (MvPolynomial.eval₂Hom E.subtype x p)
    rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
    congr 2
    ext c
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul c
  rw [he, show MvPolynomial.aeval x p = 0 from hp, map_zero]

end

end GroupActions.Variety
