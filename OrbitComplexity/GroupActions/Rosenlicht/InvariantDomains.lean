import OrbitComplexity.GroupActions.Rosenlicht.InvariantMaps
import OrbitComplexity.GroupActions.Varieties.GenericBaseFibres

/-!
# Morphisms defined by invariant rational functions

The rational map to the invariant-field model is defined over the base field.
On its maximal domain it is a dominant morphism of varieties, so its fibres
satisfy the generic dimension formula.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable (K : Type u) [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsIntegral X]
variable (E : IntermediateField K X.functionField) [Algebra.EssFiniteType K E]

/-- The rational map associated to an intermediate field is defined over the base field. -/
instance intermediateRationalMap_isOver :
    letI : (fieldModel K E).scheme.Over (Spec (.of K)) := ⟨(fieldModel K E).toSpec⟩
    (intermediateRationalMap K E).IsOver (Spec (.of K)) := by
  let _ : (fieldModel K E).scheme.Over (Spec (.of K)) := ⟨(fieldModel K E).toSpec⟩
  unfold intermediateRationalMap Scheme.RationalMap.ofFunctionField
  constructor
  refine ⟨_, ?_, rfl⟩
  constructor
  exact Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _

namespace Variety

variable {K} (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- The model of the invariant field is affine. -/
instance invariantModel_isAffine : IsAffine (invariantModel H X).scheme := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  change IsAffine (Spec (.of (fieldModelAlgebra K (invariantField H X))))
  infer_instance

/-- The rational map defined by invariant functions is defined over the base field. -/
instance invariantMap_isOver :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : (invariantModel H X).scheme.Over (Spec (.of K)) :=
      ⟨(invariantModel H X).toSpec⟩
    (invariantMap H X).IsOver (Spec (.of K)) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (invariantModel H X).scheme.Over (Spec (.of K)) :=
    ⟨(invariantModel H X).toSpec⟩
  have := invariantField_essFiniteType H X
  exact intermediateRationalMap_isOver K (invariantField H X)

/-- The domain on which all coordinates of the invariant-field model are regular. -/
def invariantDomain : GroupActions.Variety K :=
  X.openSubvariety (invariantMap H X).domain

/-- The domain of the invariant rational map is nonempty. -/
theorem invariantDomain_nonempty :
    ((invariantMap H X).domain : Set X.scheme).Nonempty :=
  (invariantMap H X).dense_domain.nonempty

/-- The domain of the invariant rational map is irreducible. -/
instance invariantDomain_irreducible : IrreducibleSpace (invariantDomain H X).scheme := by
  have : Nonempty ((invariantMap H X).domain : Scheme) :=
    Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  exact (invariantMap H X).domain.ι.isOpenEmbedding.irreducibleSpace

/-- Restricting to the domain of the invariant rational map preserves dimension. -/
theorem invariantDomain_dim : (invariantDomain H X).dim = X.dim :=
  X.openSubvariety_dim _ (invariantDomain_nonempty H X)

/-- The invariant rational map, regarded as a morphism on its domain of definition. -/
def invariantMorphism : (invariantDomain H X).toOver ⟶ (invariantModel H X).toOver := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : (invariantModel H X).scheme.Over (Spec (.of K)) :=
    ⟨(invariantModel H X).toSpec⟩
  have := invariantMap_isOver H X
  exact (invariantMap H X).toPartialMap.hom.asOver (Spec (.of K))

/-- The morphism defined by invariant functions is dominant. -/
instance invariantMorphism_dominant : IsDominant (invariantMorphism H X).left := by
  change IsDominant (invariantMap H X).toPartialMap.hom
  apply (Scheme.PartialMap.isDominant_toRationalMap_iff _).mp
  rw [Scheme.RationalMap.toRationalMap_toPartialMap]
  infer_instance

end Variety

end

end GroupActions
