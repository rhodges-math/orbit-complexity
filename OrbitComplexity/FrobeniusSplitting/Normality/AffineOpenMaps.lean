import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.OpenCovers
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine Open Maps

Principal localization isomorphisms detect affine open immersions.
-/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- Localized isomorphisms on principal target opens covering the source give an open immersion. -/
theorem isOpenImmersion_of_away_maps {A B : Type u} [CommRing A] [CommRing B]
    {I : Type*} (f : A →+* B) (a : I → A)
    (hcover : Ideal.span (Set.range (fun i ↦ f (a i))) = ⊤)
    (hlocal : ∀ i, Function.Bijective (Localization.awayMap f (a i))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  apply isOpenImmersion_of_restrict_cover (Spec.map (CommRingCat.ofHom f))
    (fun i ↦ PrimeSpectrum.basicOpen (a i))
  · change (⨆ i, TopologicalSpace.Opens.comap
      ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩
        (PrimeSpectrum.basicOpen (a i))) = ⊤
    simpa only [PrimeSpectrum.comap_basicOpen] using
      (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hcover)
  · intro i
    have : IsIso (CommRingCat.ofHom (Localization.awayMap f (a i))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hlocal i)
    exact (MorphismProperty.arrow_mk_iso_iff (@IsOpenImmersion)
      (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom f) (a i))).mpr inferInstance

end FrobeniusSplitting
