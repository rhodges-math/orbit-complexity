import OrbitComplexity.FrobeniusSplitting.Normality.Covers.GenericCoverOpens

/-! # A common principal open for finitely many morphisms -/

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

universe u v

namespace FrobeniusSplitting

/-- Finitely many morphisms surjective over the generic point of an integral
coefficient base are all surjective over one nonempty principal base open. -/
theorem exists_finite_surjective_base_open
    {R : Type u} [hR : CommRing R] [hdom : IsDomain R]
    {I : Type v} [Finite I] (X Y : I → Scheme.{u})
    [hcompact : ∀ i, CompactSpace (Y i)]
    [hqs : ∀ i, QuasiSeparatedSpace (Y i)]
    (f : ∀ i, X i ⟶ Y i) (base : ∀ i, Y i ⟶ Spec (.of R))
    [hfp : ∀ i, LocallyOfFinitePresentation (f i)]
    [hqc : ∀ i, QuasiCompact (f i)]
    [hbfp : ∀ i, LocallyOfFinitePresentation (base i)]
    [hbqc : ∀ i, QuasiCompact (base i)]
    (hgeneric : ∀ i (y : Y i), (base i y).asIdeal = ⊥ →
      y ∈ Set.range (f i)) :
    ∃ r : R, r ≠ 0 ∧
      ∀ i (y : Y i), base i y ∈ PrimeSpectrum.basicOpen r →
        y ∈ Set.range (f i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hsingle := fun i ↦
    @exists_surjective_base_open.{u} R hR hdom (X i) (Y i)
      (hcompact i) (hqs i) (f i) (base i) (hfp i) (hqc i)
      (hbfp i) (hbqc i) (hgeneric i)
  choose r hr hsurj using hsingle
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hr i), ?_⟩
  intro i y hy
  apply hsurj i y
  change r i ∉ (base i y).asIdeal
  change (∏ j, r j) ∉ (base i y).asIdeal at hy
  intro hi
  apply hy
  obtain ⟨s, hs⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
  rw [hs]
  exact (base i y).asIdeal.mul_mem_right s hi

end FrobeniusSplitting
