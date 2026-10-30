import OrbitComplexity.FrobeniusSplitting.Normality.FiniteConductor
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Conductors and localization

Inverse images of ideals commute with localization of an algebra. An ideal
contained in the base image stays in the base image after localization.

## Main results

* `FrobeniusSplitting.comap_map_localization`: inverse images commute with localization.
* `FrobeniusSplitting.map_subset_range_localization`: preservation of containment
  in the base image.
* `FrobeniusSplitting.subsingleton_quotient_of_surjective`: local surjectivity
  annihilates the localized quotient module.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting

open IsLocalization

variable {A B Aₘ Bₘ : Type*} [CommRing A] [CommRing B] [CommRing Aₘ] [CommRing Bₘ]
    [Algebra A B] (M : Submonoid A) [Algebra A Aₘ] [IsLocalization M Aₘ]
    [Algebra B Bₘ] [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]
    [Algebra A Bₘ] [Algebra Aₘ Bₘ] [IsScalarTower A B Bₘ] [IsScalarTower A Aₘ Bₘ]

include M

/-- Taking the inverse image of an ideal commutes with localization of an algebra. -/
theorem comap_map_localization (ideal : Ideal B) :
    (ideal.map (algebraMap B Bₘ)).comap (algebraMap Aₘ Bₘ) =
      (ideal.comap (algebraMap A B)).map (algebraMap A Aₘ) := by
  ext x
  obtain ⟨a, s, rfl⟩ := exists_mk'_eq M x
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mk' B,
    IsLocalization.mk'_mem_map_algebraMap_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff M]
  constructor
  · rintro ⟨t, ⟨m, hm, rfl⟩, hmem⟩
    exact ⟨m, hm, by simpa only [Ideal.mem_comap, (algebraMap A B).map_mul] using hmem⟩
  · rintro ⟨m, hm, hmem⟩
    refine ⟨algebraMap A B m, ⟨m, hm, rfl⟩, ?_⟩
    simpa only [Ideal.mem_comap, (algebraMap A B).map_mul] using hmem

/-- An ideal contained in the base image stays contained in that image after localization. -/
theorem map_subset_range_localization (ideal : Ideal B)
    (hideal : (ideal : Set B) ⊆ Set.range (algebraMap A B)) :
    (ideal.map (algebraMap B Bₘ) : Set Bₘ) ⊆ Set.range (algebraMap Aₘ Bₘ) := by
  intro x hx
  obtain ⟨⟨⟨b, hb⟩, ⟨t, ht⟩⟩, heq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid B M) Bₘ).1 hx
  obtain ⟨s, hs, rfl⟩ := ht
  obtain ⟨a, rfl⟩ := hideal hb
  refine ⟨mk' Aₘ a ⟨s, hs⟩, ?_⟩
  rw [IsLocalization.algebraMap_mk' B, IsLocalization.mk'_eq_iff_eq_mul]
  exact heq.symm

/-- Surjectivity of a localized algebra map annihilates the localized quotient module. -/
theorem subsingleton_quotient_of_surjective
    (hsurjective : Function.Surjective (algebraMap Aₘ Bₘ)) :
    Subsingleton (LocalizedModule M (B ⧸ (⊥ : Subalgebra A B).toSubmodule)) := by
  have hlocalized : Function.Surjective
      (IsLocalizedModule.map M (Algebra.linearMap A Aₘ)
        (IsScalarTower.toAlgHom A B Bₘ).toLinearMap (Algebra.linearMap A B)) := by
    rw [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ M Aₘ Bₘ]
    change Function.Surjective (IsLocalization.mapₐ M Aₘ Aₘ Bₘ (Algebra.ofId A B))
    intro b
    obtain ⟨a, rfl⟩ := hsurjective b
    refine ⟨a, ?_⟩
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (IsLocalization.mapₐ M Aₘ Aₘ Bₘ (Algebra.ofId A B)).commutes a
  have hcanonical :=
    (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
      (Algebra.linearMap A Aₘ) (IsScalarTower.toAlgHom A B Bₘ).toLinearMap).1 hlocalized
  have hquotient :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
      M (Algebra.linearMap A B)).1 hcanonical
  have hrange : (Algebra.linearMap A B).range = (⊥ : Subalgebra A B).toSubmodule := by
    ext b
    rfl
  exact (congrArg (fun N : Submodule A B ↦ Subsingleton (LocalizedModule M (B ⧸ N)))
    hrange).mp hquotient

end FrobeniusSplitting
