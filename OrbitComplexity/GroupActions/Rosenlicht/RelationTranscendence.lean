import OrbitComplexity.GroupActions.Rosenlicht.RelationFields
import OrbitComplexity.GroupActions.Rosenlicht.RelationKernels
import OrbitComplexity.GroupActions.Varieties.FunctionFieldDimension

/-!
# Transcendence degree of orbit relation fields

The first projection's relative function field is presented by the generic
orbit relation ideal. Its transcendence degree is therefore the transcendence
degree of the original function field over invariant functions. Dimension in
the tower then computes the dimension of the relation closure.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The relative function field of the orbit relation has the transcendence
degree of the original function field over invariant rational functions. -/
theorem orbitRelationField_trdeg {ι : Type v} [Finite ι]
    (x : ι → X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
      ⟨(orbitRelationVariety H X).toSpec⟩
    letI : IsIntegral (orbitRelationVariety H X).scheme :=
      isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
    letI : Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
      (relationFirstFieldMap H X).toAlgebra
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      (Algebra.trdeg X.scheme.functionField
        (orbitRelationVariety H X).scheme.functionField).toNat =
          (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
    ⟨(orbitRelationVariety H X).toSpec⟩
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let _ : Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
    (relationFirstFieldMap H X).toAlgebra
  intro hx
  have hd := relationQuotient_dim X.scheme.functionField
    (orbitRelationVariety H X).scheme.functionField
    (fun i ↦ relationSecondFieldMap H X (x i)) (orbitRelationField_generators H X x hx)
  have hk : RingHom.ker (MvPolynomial.aeval
      (fun i ↦ relationSecondFieldMap H X (x i)) :
        MvPolynomial ι X.scheme.functionField →ₐ[X.scheme.functionField]
          (orbitRelationVariety H X).scheme.functionField) = genericOrbitIdeal H X x :=
    relationField_ker_eq H X x
  rw [hk] at hd
  have hi : IntermediateField.adjoin K (Set.range x) ≤
      (IntermediateField.adjoin (invariantField H X) (Set.range x)).restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    exact IntermediateField.subset_adjoin (invariantField H X) _
  have hxE : IntermediateField.adjoin (invariantField H X) (Set.range x) = ⊤ := by
    apply top_le_iff.mp
    intro f _
    exact hi (by rw [hx]; trivial)
  have hn := hd.symm.trans (genericOrbitIdeal_dim H X x hxE)
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hn)

/-- The dimension of the orbit relation closure is the ambient dimension plus
transcendence degree over invariant rational functions. -/
theorem orbitRelation_dim_add :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    (orbitRelationVariety H X).dim = X.dim +
      ((Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat : WithBot ℕ∞) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
    ⟨(orbitRelationVariety H X).toSpec⟩
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let _ : Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
    (relationFirstFieldMap H X).toAlgebra
  let _ : (orbitRelationProjection H X).left.IsOver (Spec (.of K)) :=
    ⟨(orbitRelationProjection H X).w⟩
  have : IsScalarTower K X.scheme.functionField
      (orbitRelationVariety H X).scheme.functionField :=
    IsScalarTower.of_algHom (functionFieldAlgHom K (X := (orbitRelationVariety H X).scheme)
      (Y := X.scheme) (orbitRelationProjection H X).left)
  have : LocallyOfFiniteType (X.scheme ↘ Spec (.of K)) := X.locallyOfFiniteType
  have : LocallyOfFiniteType ((orbitRelationVariety H X).scheme ↘ Spec (.of K)) :=
    (orbitRelationVariety H X).locallyOfFiniteType
  have : Algebra.EssFiniteType K X.scheme.functionField := inferInstance
  have : Algebra.EssFiniteType K (orbitRelationVariety H X).scheme.functionField := inferInstance
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K X.scheme.functionField
  let x : s → X.scheme.functionField := Subtype.val
  have hx : IntermediateField.adjoin K (Set.range x) = ⊤ := by
    have hxr : Set.range x = (s : Set X.scheme.functionField) := by
      ext f
      constructor
      · rintro ⟨a, rfl⟩
        exact a.property
      · intro hf
        exact ⟨⟨f, hf⟩, rfl⟩
    rw [hxr]
    exact hs
  have hr := orbitRelationField_trdeg H X x hx
  have ht := trdeg_add_eq K X.scheme.functionField
    (A := (orbitRelationVariety H X).scheme.functionField)
  have hf := Cardinal.add_lt_aleph0_iff.mp
    (ht ▸ trdeg_lt_aleph0 K (orbitRelationVariety H X).scheme.functionField)
  have hn := congrArg Cardinal.toNat ht
  rw [Cardinal.toNat_add hf.1 hf.2, hr] at hn
  have hd : (orbitRelationVariety H X).natDim = X.natDim +
      (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat := by
    rw [(orbitRelationVariety H X).natDim_functionField, X.natDim_functionField]
    exact hn.symm
  rw [← (orbitRelationVariety H X).natDim_cast, ← X.natDim_cast, hd, Nat.cast_add]

end

end GroupActions.Variety
