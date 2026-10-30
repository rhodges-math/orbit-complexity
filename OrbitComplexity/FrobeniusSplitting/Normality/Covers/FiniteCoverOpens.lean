import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.GenericCoverOpens
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Opens over which a finite family covers -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v

/-- A finite family covering the generic fibre covers every point over some
nonempty principal open of its integral coefficient base. -/
theorem exists_finite_cover_base_open {R : Type u} [CommRing R] [IsDomain R]
    {I : Type v} [Finite I] {Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ Y) (base : Y ⟶ Spec (.of R))
    [∀ i, LocallyOfFinitePresentation (f i)] [∀ i, QuasiCompact (f i)]
    [LocallyOfFinitePresentation base] [QuasiCompact base]
    (hgeneric : ∀ y : Y, (base y).asIdeal = ⊥ → ∃ i x, f i x = y) :
    ∃ r : R, r ≠ 0 ∧
      ∀ y : Y, base y ∈ PrimeSpectrum.basicOpen r → ∃ i x, f i x = y := by
  have hcompact : ∀ i, CompactSpace (X i) :=
    fun i ↦ QuasiCompact.compactSpace_of_compactSpace (f i)
  have : Finite (sigmaOpenCover X).I₀ := by change Finite I; infer_instance
  let : ∀ i, CompactSpace ((sigmaOpenCover X).X i) := by
    intro i
    change I at i
    change CompactSpace (X i)
    exact hcompact i
  let : CompactSpace (∐ X : Scheme.{u}) := (sigmaOpenCover X).compactSpace
  let q : (∐ X : Scheme.{u}) ⟶ Y := Sigma.desc f
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  have : LocallyOfFinitePresentation q :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ inferInstance)
  have : QuasiCompact q := inferInstance
  obtain ⟨r, hr, hcover⟩ := exists_surjective_base_open q base (fun y hy ↦ by
    obtain ⟨i, x, hx⟩ := hgeneric y hy
    refine ⟨Sigma.ι X i x, ?_⟩
    simpa only [q, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using hx)
  refine ⟨r, hr, fun y hy ↦ ?_⟩
  obtain ⟨z, hz⟩ := hcover y hy
  obtain ⟨i, x, rfl⟩ := (sigmaOpenCover X).exists_eq z
  change I at i
  change X i at x
  change q (Sigma.ι X i x) = y at hz
  refine ⟨i, x, ?_⟩
  simpa only [q, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using hz

end FrobeniusSplitting
