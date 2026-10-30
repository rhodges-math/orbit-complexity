import OrbitComplexity.GroupActions.Rosenlicht.GenericFieldFibres
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Dimension of generic orbit relations

The dimension of the scalar extension of a finite-type domain is the
transcendence degree of its fraction field. The presentation by invariant
relations therefore computes the dimension of the generic orbit relation ideal.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w z

/-- Extending the scalars of a finite-type domain to a field gives the
transcendence degree of the domain's fraction field as its Krull dimension. -/
theorem ringKrullDim_tensor_fraction (E : Type u) [Field E]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra E A] [Algebra.FiniteType E A]
    (F : Type w) [Field F] [Algebra E F] [Algebra A F]
    [IsScalarTower E A F] [IsFractionRing A F]
    (L : Type z) [Field L] [Algebra E L] :
    ringKrullDim (L ⊗[E] A) = (Algebra.trdeg E F).toNat := by
  rw [TauCeti.ringKrullDim_tensorProduct_field_of_finiteType,
    TauCeti.ringKrullDim_eq_toNat_trdeg E A]
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have h := lift_trdeg_add_eq E A F
  rw [trdeg_eq_zero (R := A) (A := F), Cardinal.lift_zero, add_zero] at h
  have ht : (Algebra.trdeg E A).toNat = (Algebra.trdeg E F).toNat := by
    simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat h
  exact congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞)) ht

section Orbit

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {G : Type w} [Group G] [MulSemiringAction G F] [SMulCommClass G K F]
variable {ι : Type z} [Finite ι]

/-- The generic orbit relation quotient has dimension equal to the transcendence
degree over the invariant field, when the tuple generates the ambient field. -/
theorem orbitIdeal_quotient_dim (x : ι → F)
    (hx : IntermediateField.adjoin
      (FixedPoints.intermediateField (F := K) G : IntermediateField K F)
      (Set.range x) = ⊤) :
    ringKrullDim (MvPolynomial ι F ⧸ orbitIdeal (G := G) x) =
      (Algebra.trdeg
        (FixedPoints.intermediateField (F := K) G : IntermediateField K F) F).toNat := by
  let E := (FixedPoints.intermediateField (F := K) G : IntermediateField K F)
  have : IsFractionRing (Algebra.adjoin E (Set.range x)) F := adjoin_isFractionRing E x hx
  have : Algebra.FiniteType E (Algebra.adjoin E (Set.range x)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range x)
  obtain ⟨e⟩ := exists_fixedFieldTensorEquiv (K := K) (G := G) x
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_tensor_fraction E (Algebra.adjoin E (Set.range x)) F F

end Orbit

namespace Variety

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]
variable {ι : Type z} [Finite ι]

/-- The polynomial quotient defining generic orbit relations has dimension the
transcendence degree of the function field over invariant functions. -/
theorem genericOrbitIdeal_dim (x : ι → X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    IntermediateField.adjoin (invariantField H X) (Set.range x) = ⊤ →
      ringKrullDim (MvPolynomial ι X.scheme.functionField ⧸ genericOrbitIdeal H X x) =
        (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ := functionFieldAction (schemeTranslationHom H X)
  have : SMulCommClass H.points K X.scheme.functionField :=
    functionFieldAction_smulComm K (translationHom H X)
  exact orbitIdeal_quotient_dim (K := K) (G := H.points) x

end Variety

end

end GroupActions
