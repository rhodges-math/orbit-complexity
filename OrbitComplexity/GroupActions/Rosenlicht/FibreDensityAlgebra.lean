import OrbitComplexity.GroupActions.Rosenlicht.FiniteTypeKernels
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Generic density in prime fibres
-/

open MvPolynomial
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w z

/-- An injective map between finite-type algebras over a Noetherian domain
remains injective under every scalar extension after one denominator is inverted. -/
theorem exists_tensorMap_injective
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (f : B →ₐ[R] A) (hf : Function.Injective f) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type z) [CommRing C] [Algebra R C],
      IsUnit (algebraMap R C d) →
        Function.Injective (Algebra.TensorProduct.map (AlgHom.id C C) f) := by
  obtain ⟨n, p, hp⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp
    inferInstance
  obtain ⟨d, hd, hker⟩ := exists_polynomial_kernel_baseChange R A n (f.comp p)
  refine ⟨d, hd, ?_⟩
  intro C _ _ hunit
  have hpker : RingHom.ker (polynomialTensorMap C p) =
      (RingHom.ker p).map (MvPolynomial.map (algebraMap R C)) := by
    apply ker_polynomialTensorMap C p ⊥
    rw [LinearMap.range_eq_top.mpr hp]
    exact isCompl_top_bot
  have hfp : RingHom.ker (f.comp p) = RingHom.ker p :=
    RingHom.ker_comp_of_injective p.toRingHom hf
  have hk : RingHom.ker (polynomialTensorMap C (f.comp p)) =
      RingHom.ker (polynomialTensorMap C p) := by
    rw [hker C hunit, hfp, hpker]
  have hps : Function.Surjective (polynomialTensorMap C p) :=
    (Algebra.TensorProduct.map_surjective (AlgHom.id C C) p
      (Function.surjective_id) hp).comp
      (MvPolynomial.algebraTensorAlgEquiv R C).symm.surjective
  intro a b hab
  obtain ⟨q, rfl⟩ := hps a
  obtain ⟨r, rfl⟩ := hps b
  have hqr : q - r ∈ RingHom.ker (polynomialTensorMap C (f.comp p)) := by
    rw [polynomialTensorMap_comp]
    change (Algebra.TensorProduct.map (AlgHom.id C C) f)
      (polynomialTensorMap C p (q - r)) = 0
    simpa only [map_sub, sub_eq_zero] using hab
  rw [hk] at hqr
  have hz : polynomialTensorMap C p (q - r) = 0 := hqr
  simpa only [map_sub, sub_eq_zero] using hz

/-- A dominant affine morphism between spectra of finite-type algebras stays
dominant under all coefficient extensions after one base denominator is inverted. -/
theorem exists_baseChange_denseRange
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (f : B →ₐ[R] A) (hf : Function.Injective f) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type z) [CommRing C] [Algebra R C],
      IsUnit (algebraMap R C d) →
        DenseRange (PrimeSpectrum.comap
          (Algebra.TensorProduct.map (AlgHom.id C C) f).toRingHom) := by
  obtain ⟨d, hd, heq⟩ := exists_tensorMap_injective R B A f hf
  refine ⟨d, hd, ?_⟩
  intro C _ _ hu
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot
    (Algebra.TensorProduct.map (AlgHom.id C C) f).toRingHom).mp (heq C hu)]
  exact bot_le

end

end GroupActions

open scoped TensorProduct nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w

/-- A principal open subset of an integral finite-type algebra is dense in
every coefficient fibre after one nonzero base denominator is inverted. -/
theorem exists_baseChange_basicOpen_dense
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    (b : B) (hb : b ≠ 0) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type w) [CommRing C] [Algebra R C],
      IsUnit (algebraMap R C d) →
        Dense (PrimeSpectrum.basicOpen ((1 : C) ⊗ₜ[R] b) :
          Set (PrimeSpectrum (C ⊗[R] B))) := by
  let g : B →ₐ[R] Localization.Away b :=
    IsScalarTower.toAlgHom R B (Localization.Away b)
  have hg : Function.Injective g := by
    apply IsLocalization.injective (M := Submonoid.powers b) (Localization.Away b)
    rw [Submonoid.powers_le]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hb
  obtain ⟨d, hd, hdense⟩ := exists_baseChange_denseRange R B (Localization.Away b) g hg
  refine ⟨d, hd, ?_⟩
  intro C _ _ hu
  let φ := Algebra.TensorProduct.map (AlgHom.id C C) g
  let : Algebra (C ⊗[R] B) (C ⊗[R] Localization.Away b) := φ.toAlgebra
  have : IsScalarTower C (C ⊗[R] B) (C ⊗[R] Localization.Away b) :=
    .of_algebraMap_eq fun c ↦ by
      simp [φ, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right R C
    (Submonoid.powers b) (Localization.Away b) (by
      ext x
      simp [φ, g, RingHom.algebraMap_toAlgebra])
  have : IsLocalization.Away ((1 : C) ⊗ₜ[R] b)
      (C ⊗[R] Localization.Away b) := by
    simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using hloc
  rw [← PrimeSpectrum.localization_away_comap_range
    (C ⊗[R] Localization.Away b) ((1 : C) ⊗ₜ[R] b)]
  exact hdense C hu

end

end GroupActions

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v

/-- A principal open in an integral finite-type algebra meets a dense subset of
each prime fibre over a nonempty principal open in the base. -/
theorem exists_basicOpen_dense_fibres
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    (b : B) (hb : b ≠ 0) :
    ∃ d : R, d ≠ 0 ∧ ∀ p ∈ PrimeSpectrum.basicOpen d,
      Dense {q : PrimeSpectrum.comap (algebraMap R B) ⁻¹' {p} |
        q.val ∈ PrimeSpectrum.basicOpen b} := by
  obtain ⟨d, hd, hdense⟩ := exists_baseChange_basicOpen_dense R B b hb
  refine ⟨d, hd, ?_⟩
  intro p hp
  have hu : IsUnit (algebraMap R p.asIdeal.ResidueField d) := by
    rw [isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]
    exact (PrimeSpectrum.mem_basicOpen d p).mp hp
  have hD := hdense p.asIdeal.ResidueField hu
  let h := PrimeSpectrum.preimageHomeomorphFiber R B p
  have hi := h.symm.surjective.denseRange.dense_image h.symm.continuous hD
  have he : h.symm '' (PrimeSpectrum.basicOpen
      ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] b) :
        Set (PrimeSpectrum (p.asIdeal.Fiber B))) =
      {q : PrimeSpectrum.comap (algebraMap R B) ⁻¹' {p} |
        q.val ∈ PrimeSpectrum.basicOpen b} := by
    ext q
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hq
      obtain ⟨r, rfl⟩ := h.symm.surjective q
      exact ⟨r, hq, rfl⟩
  rwa [he] at hi

end

end GroupActions
