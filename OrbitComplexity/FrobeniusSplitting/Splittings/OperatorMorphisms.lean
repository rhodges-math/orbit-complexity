import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorSpec

/-!
# Naturality of affine scheme operators

A homomorphism commuting with ring operators induces a morphism of spectra
commuting with the corresponding operators on all open subsets. This follows
from the localization formula at each prime ideal.

## Main results

* `FrobeniusSplitting.FrobeniusLinearMap.toSpec_naturality`: naturality on all sections.
-/

namespace FrobeniusSplitting.FrobeniusLinearMap

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {p : ℕ}

private theorem localRingHom_commute (source : FrobeniusLinearMap R p)
    (target : FrobeniusLinearMap S p) (hp : 0 < p) (f : R →+* S)
    (hf : ∀ a, target (f a) = f (source a)) (P : PrimeSpectrum S)
    (a : Localization (PrimeSpectrum.comap f P).asIdeal.primeCompl) :
    target.localize P.asIdeal.primeCompl hp
      (Localization.localRingHom (PrimeSpectrum.comap f P).asIdeal P.asIdeal f
        (PrimeSpectrum.comap_asIdeal f P) a) =
    Localization.localRingHom (PrimeSpectrum.comap f P).asIdeal P.asIdeal f
      (PrimeSpectrum.comap_asIdeal f P)
      (source.localize (PrimeSpectrum.comap f P).asIdeal.primeCompl hp a) := by
  apply source.map_localize _ hp _ _
  intro a
  rw [Localization.localRingHom_to_map, localize_algebraMap,
    Localization.localRingHom_to_map, hf]

/-- A homomorphism commuting with operators induces a compatible morphism of spectra. -/
theorem toSpec_naturality (source : FrobeniusLinearMap R p) (target : FrobeniusLinearMap S p)
    (hp : 0 < p) (f : R →+* S) (hf : ∀ a, target (f a) = f (source a))
    (U : (Spec (.of R)).Opens) (s : Γ(Spec (.of R), U)) :
    (target.toSpec hp).onOpen ((Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ U)
        ((Spec.map (CommRingCat.ofHom f)).app U s) =
      (Spec.map (CommRingCat.ofHom f)).app U ((source.toSpec hp).onOpen U s) := by
  apply Subtype.ext
  funext x
  change target.localize (S := Localization x.1.asIdeal.primeCompl)
    x.1.asIdeal.primeCompl hp
      ((StructureSheaf.comap f U ((Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ U) (fun _ hx ↦ hx) s).1 x) =
    (StructureSheaf.comap f U ((Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ U) (fun _ hx ↦ hx)
      ((source.toSpec hp).onOpen U s)).1 x
  erw [StructureSheaf.comap_apply, StructureSheaf.comap_apply]
  change target.localize x.1.asIdeal.primeCompl hp
    (Localization.localRingHom (PrimeSpectrum.comap f x.1).asIdeal x.1.asIdeal f rfl
      (s.1 ⟨PrimeSpectrum.comap f x.1, x.2⟩)) =
    Localization.localRingHom (PrimeSpectrum.comap f x.1).asIdeal x.1.asIdeal f rfl
      (source.localize (PrimeSpectrum.comap f x.1).asIdeal.primeCompl hp
        (s.1 ⟨PrimeSpectrum.comap f x.1, x.2⟩))
  exact localRingHom_commute source target hp f hf x.1 _

end FrobeniusSplitting.FrobeniusLinearMap
