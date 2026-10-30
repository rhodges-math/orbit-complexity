import Batteries.Tactic.Lint
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization Maps

Bijective localization maps detect bijectivity of the canonical away map.
-/

namespace FrobeniusSplitting

/-- Bijectivity of a commuting map between principal localizations holds for canonical models. -/
theorem awayMap_bijective_of_localizations {A B A' B' : Type*}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A A'] [Algebra B B'] (f : A →+* B) (a : A)
    [IsLocalization.Away a A'] [IsLocalization.Away (f a) B']
    (g : A' →+* B')
    (hcomm : g.comp (algebraMap A A') = (algebraMap B B').comp f)
    (hbij : Function.Bijective g) : Function.Bijective (Localization.awayMap f a) := by
  have hg : g = IsLocalization.Away.map A' B' f a := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    rw [hcomm]
    ext x
    change algebraMap B B' (f x) = IsLocalization.Away.map A' B' f a (algebraMap A A' x)
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
  rw [hg] at hbij
  refine ⟨Localization.awayMap_injective_iff.mpr ?_, Localization.awayMap_surjective_iff.mpr ?_⟩
  · exact (IsLocalization.Away.map_injective_iff (S := A') B' f a).mp hbij.1
  · exact (IsLocalization.Away.map_surjective_iff A' B' f a).mp hbij.2

end FrobeniusSplitting
