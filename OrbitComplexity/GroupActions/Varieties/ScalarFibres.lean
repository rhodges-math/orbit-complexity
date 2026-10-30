import OrbitComplexity.GroupActions.Varieties.NormalizationFibres

/-! # Scalar fibres of localized algebras

Tensoring a localized algebra with an algebra over the localized base recovers the
scalar fibre of the original algebra. Polynomial normalization therefore gives a single
open part of the base where every field fibre has the generic dimension.
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

/-- Scalar fibres of a simultaneous localization agree with those of the original algebra. -/
def localizationFibreEquiv {R A R' A' L : Type u} [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] [CommRing L] [Algebra R A] [Algebra R R']
    [Algebra A A'] [Algebra R A'] [Algebra R' A'] [IsScalarTower R A A']
    [IsScalarTower R R' A'] [Algebra R L] [Algebra R' L] [IsScalarTower R R' L]
    (M : Submonoid R) [IsLocalization M R']
    [IsLocalization (Algebra.algebraMapSubmonoid A M) A'] :
    (L ⊗[R'] A') ≃+* (L ⊗[R] A) := by
  let : Algebra.IsPushout R R' A A' :=
    Algebra.IsPushout.symm (Algebra.isPushout_of_isLocalization M R' A A')
  exact (Algebra.TensorProduct.congr (.refl : L ≃ₐ[R'] L)
    (Algebra.IsPushout.equiv R R' A A').symm).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange R R' L L A).toRingEquiv

/-- One base denominator makes every remaining field fibre have the generic dimension. -/
theorem exists_field_fibre_dim {R A k B : Type u} [CommRing R] [CommRing A]
    [Field k] [CommRing B] [Algebra R A] [Algebra R k] [Algebra A B] [Algebra R B]
    [Algebra k B] [IsScalarTower R A B] [IsScalarTower R k B] (M : Submonoid R)
    [IsLocalization M k] [IsLocalization (Algebra.algebraMapSubmonoid A M) B]
    [Nontrivial B] [Algebra.FiniteType k B] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R k)) :
    ∃ m : M, ∀ (L : Type u) [Field L] [Algebra R L],
      IsUnit (algebraMap R L (m : R)) → ringKrullDim (L ⊗[R] A) = ringKrullDim B := by
  obtain ⟨m, hm⟩ := exists_constant_fibre_dim (A := A) (k := k) (B := B) M hinj
  refine ⟨m, ?_⟩
  intro L _ _ hmunit
  let R' := Localization.Away (m : R)
  let A' := Localization.Away (algebraMap R A (m : R))
  let : Algebra R' A' := (Localization.awayMap (algebraMap R A) (m : R)).toAlgebra
  let : Algebra R' L := (Localization.awayLift (algebraMap R L) (m : R) hmunit).toAlgebra
  have : IsScalarTower R R' A' :=
    .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsScalarTower R R' L :=
    .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers (m : R))) A' := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  change ∀ (L : Type u) [Field L] [Algebra R' L],
    ringKrullDim (L ⊗[R'] A') = ringKrullDim B at hm
  exact (ringKrullDim_eq_of_ringEquiv
    (localizationFibreEquiv (A := A) (R' := R') (A' := A') (L := L)
      (Submonoid.powers (m : R)))).symm.trans (hm L)

end

end GroupActions
