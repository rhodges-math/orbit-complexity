import OrbitComplexity.GroupActions.Rosenlicht.RelationFibres
import OrbitComplexity.GroupActions.Rosenlicht.TensorFractions

/-!
# Integral generic field relations

Passing a relation algebra to its fraction field preserves the integrality of
its scalar extension. For an irreducible group action, this applies to the
function field over its invariant subfield.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w z

/-- Localizing one factor of an integral tensor product to its fraction field
preserves integrality. -/
theorem tensorFraction_isDomain (K : Type u) [Field K]
    (A : Type v) [CommRing A] [Algebra K A]
    (F : Type w) [Field F] [Algebra K F] [Algebra A F]
    [IsScalarTower K A F] [IsFractionRing A F]
    (B : Type z) [CommRing B] [Algebra K B] [IsDomain (A ⊗[K] B)] :
    IsDomain (F ⊗[K] B) := by
  let e := tensorFractionEquiv K A F B
  exact Function.Injective.isDomain
    (e.toRingHom.comp (algebraMap (F ⊗[K] B) (FractionRing (F ⊗[K] B))))
    (e.injective.comp (IsFractionRing.injective _ _))

/-- A tuple that generates a field generates an algebra with that field as its
fraction field. -/
theorem adjoin_isFractionRing (E : Type u) [Field E]
    {F : Type v} [Field F] [Algebra E F] {ι : Type w} (x : ι → F)
    (hx : IntermediateField.adjoin E (Set.range x) = ⊤) :
    IsFractionRing (Algebra.adjoin E (Set.range x)) F := by
  apply IsFractionRing.of_field
  intro f
  have hf : f ∈ IntermediateField.adjoin E (Set.range x) := by rw [hx]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp hf
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩

namespace Variety

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The tensor product of an integral variety's function field with itself over
its invariant field is integral for an irreducible acting group. -/
theorem invariantFieldTensor_isDomain :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    IsDomain (X.scheme.functionField ⊗[invariantField H X] X.scheme.functionField) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let F := X.scheme.functionField
  let E := invariantField H X
  have : LocallyOfFiniteType (X.scheme ↘ Spec (.of K)) := X.locallyOfFiniteType
  have : Algebra.EssFiniteType K F := by
    dsimp only [F]
    infer_instance
  have : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp K E F
  obtain ⟨t, ht⟩ := IntermediateField.fg_top E F
  let x : t → F := Subtype.val
  have hxr : Set.range x = (t : Set F) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  have hx : IntermediateField.adjoin E (Set.range x) = ⊤ := by
    rw [hxr]
    exact ht
  have : IsFractionRing (Algebra.adjoin E (Set.range x)) F := adjoin_isFractionRing E x hx
  have : IsDomain (F ⊗[E] Algebra.adjoin E (Set.range x)) :=
    genericOrbitTensor_isDomain H X x
  have : IsDomain ((Algebra.adjoin E (Set.range x)) ⊗[E] F) :=
    Function.Injective.isDomain
      (Algebra.TensorProduct.comm E (Algebra.adjoin E (Set.range x)) F)
      (Algebra.TensorProduct.comm E (Algebra.adjoin E (Set.range x)) F).injective
  exact tensorFraction_isDomain E (Algebra.adjoin E (Set.range x)) F F

end Variety

end

end GroupActions
