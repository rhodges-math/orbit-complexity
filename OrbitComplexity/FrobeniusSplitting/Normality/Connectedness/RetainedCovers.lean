import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedConstructible
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.FiniteCoverModels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Finite image covers retained under principal base localization

The cover certificates concern specified images of scheme morphisms. Their pullbacks are
identified by an arbitrary-scheme Cartesian-square lemma, so the conclusion applies to
all coefficient base changes, including algebraic closures of positive-characteristic
residue fields. No connectedness conclusion is assumed in these certificates.
-/

namespace FrobeniusSplitting

open CategoryTheory AlgebraicGeometry Topology Set

universe u v w

/-- The image of the bottom chart in a Cartesian square is the inverse image of its top image. -/
theorem retainedRange_of_isPullback {P X Y Z : Scheme.{u}}
    {qX : P ⟶ X} {g : P ⟶ Y} {f : X ⟶ Z} {qY : Y ⟶ Z}
    (h : IsPullback qX g f qY) : Set.range g = qY ⁻¹' Set.range f := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    Scheme.image_preimage_eq_of_isPullback h (Set.univ : Set X)

/-- Missing points of an image cover pull back exactly for specified Cartesian chart squares. -/
theorem retainedMissing_eq {I : Type v} {Y Y' : Scheme.{u}}
    (X X' : I → Scheme.{u}) (f : ∀ i, X i ⟶ Y) (g : ∀ i, X' i ⟶ Y')
    (qX : ∀ i, X' i ⟶ X i) (qY : Y' ⟶ Y)
    (hsq : ∀ i, IsPullback (qX i) (g i) (f i) qY) :
    (⋃ i, Set.range (g i))ᶜ = qY ⁻¹' (⋃ i, Set.range (f i))ᶜ := by
  ext y
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion]
  apply not_congr
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Set.ext_iff.mp (retainedRange_of_isPullback (hsq i)) y).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (Set.ext_iff.mp (retainedRange_of_isPullback (hsq i)) y).mpr hi⟩

/-- An image family covers exactly when its constructible missing-point set is empty. -/
theorem retainedCover_iff_empty {I : Type v} {Y : Scheme.{u}} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ Y) :
    (∀ y : Y, ∃ i x, f i x = y) ↔ (⋃ i, Set.range (f i))ᶜ = ∅ := by
  classical
  constructor
  · intro hcover
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨i, x, hx⟩ := hcover y
    exact hy (Set.mem_iUnion.mpr ⟨i, x, hx⟩)
  · intro hempty y
    by_contra hn
    have hy : y ∈ (⋃ i, Set.range (f i))ᶜ := by
      intro hy
      obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hy
      exact hn ⟨i, x, hx⟩
    rw [hempty] at hy
    exact hy

private theorem localization_point_basicOpen {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (r : R) [IsLocalization.Away r A] (p : PrimeSpectrum A) :
    PrimeSpectrum.comap (algebraMap R A) p ∈ PrimeSpectrum.basicOpen r := by
  have h : PrimeSpectrum.comap (algebraMap R A) p ∈
      Set.range (PrimeSpectrum.comap (algebraMap R A)) := ⟨p, rfl⟩
  rw [PrimeSpectrum.localization_away_comap_range A r] at h
  exact h

/-- Every point of the spectrum of a principal localization maps into its defining base open. -/
theorem retained_base_mem_basicOpen {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (r : R) [IsLocalization.Away r A] (p : Spec (.of A)) :
    Spec.map (CommRingCat.ofHom (algebraMap R A)) p ∈ PrimeSpectrum.basicOpen r := by
  exact localization_point_basicOpen r (show PrimeSpectrum A from p)

/-- Base localization removes a constructible exceptional set on every subsequent
  coefficient scheme. -/
theorem retainedEmpty_of_localization {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (r : R) [IsLocalization.Away r A]
    {Y S Y' : Scheme.{u}} (base : Y ⟶ Spec (.of R)) (scalar : S ⟶ Spec (.of A))
    (qY : Y' ⟶ Y) (base' : Y' ⟶ S)
    (hbase : qY ≫ base = base' ≫ scalar ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) (T : Set Y)
    (havoid : ∀ y : Y, base y ∈ PrimeSpectrum.basicOpen r → y ∉ T) :
    qY ⁻¹' T = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have he := congrArg (fun f : Y' ⟶ Spec (.of R) => f y) hbase
  have hb : base (qY y) ∈ PrimeSpectrum.basicOpen r := by
    rw [show base (qY y) = Spec.map (CommRingCat.ofHom (algebraMap R A))
      (scalar (base' y)) from by simpa only [Scheme.Hom.comp_apply] using he]
    exact retained_base_mem_basicOpen r _
  exact havoid (qY y) hb hy

/-- Specified Cartesian chart pullbacks retain an image cover after the chosen base localization. -/
theorem retainedCover_of_localization {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (r : R) [IsLocalization.Away r A]
    {I : Type v} {Y S Y' : Scheme.{u}} (X X' : I → Scheme.{u})
    (f : ∀ i, X i ⟶ Y) (g : ∀ i, X' i ⟶ Y')
    (base : Y ⟶ Spec (.of R)) (scalar : S ⟶ Spec (.of A))
    (qX : ∀ i, X' i ⟶ X i) (qY : Y' ⟶ Y) (base' : Y' ⟶ S)
    (hbase : qY ≫ base = base' ≫ scalar ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hsq : ∀ i, IsPullback (qX i) (g i) (f i) qY)
    (hcover : ∀ y : Y, base y ∈ PrimeSpectrum.basicOpen r → ∃ i x, f i x = y) :
    ∀ y : Y', ∃ i x, g i x = y := by
  apply (retainedCover_iff_empty X' g).mpr
  rw [retainedMissing_eq X X' f g qX qY hsq]
  apply retainedEmpty_of_localization r base scalar qY base' hbase
  intro y hy hmissing
  obtain ⟨i, x, hx⟩ := hcover y hy
  exact hmissing (Set.mem_iUnion.mpr ⟨i, x, hx⟩)

end FrobeniusSplitting
