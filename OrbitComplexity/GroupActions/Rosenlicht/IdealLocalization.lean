import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Equality of finitely generated ideals after one denominator

An inclusion of localized ideals can be witnessed by finitely many denominator
multiples of generators. Their product makes the inclusion hold in every algebra
where that one element is invertible. Applying both inclusions spreads equality.
-/

namespace GroupActions

noncomputable section

universe u v w z

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]

/-- An inclusion of localized ideals with finitely generated source holds in every
algebra inverting one denominator from the base ring. -/
theorem exists_localization_map_le (M : Submonoid R)
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B]
    (I J : Ideal A) (hI : I.FG)
    (hIJ : Ideal.map (algebraMap A B) I ≤ Ideal.map (algebraMap A B) J) :
    ∃ r ∈ M, ∀ (C : Type z) [CommRing C] [Algebra A C],
      IsUnit (algebraMap A C (algebraMap R A r)) →
        Ideal.map (algebraMap A C) I ≤ Ideal.map (algebraMap A C) J := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hden (a : t) : ∃ r : M, algebraMap R A r * a.val ∈ J := by
    have ha : algebraMap A B a.val ∈ Ideal.map (algebraMap A B) J :=
      hIJ (Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span a.property))
    obtain ⟨m, hm, hma⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid A M) B J a.val).mp ha
    obtain ⟨r, hr, he⟩ := hm
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [he]
    exact hma
  choose d hd using hden
  let r : R := ∏ a : t, (d a : R)
  have hr : r ∈ M := M.prod_mem (fun a _ ↦ (d a).property)
  refine ⟨r, hr, ?_⟩
  intro C _ _ hc
  rw [← ht, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  let a' : t := ⟨a, ha⟩
  have hdiv : (d a' : R) ∣ r := Finset.dvd_prod_of_mem _ (Finset.mem_univ a')
  have hdiv' : algebraMap A C (algebraMap R A (d a')) ∣
      algebraMap A C (algebraMap R A r) :=
    map_dvd (algebraMap A C) (map_dvd (algebraMap R A) hdiv)
  have hu : IsUnit (algebraMap A C (algebraMap R A (d a'))) :=
    isUnit_of_dvd_unit hdiv' hc
  have hm := Ideal.mem_map_of_mem (algebraMap A C) (hd a')
  rw [map_mul] at hm
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm

/-- Equality of localized finitely generated ideals holds in every algebra
inverting one denominator from the base ring. -/
theorem exists_localization_map_eq (M : Submonoid R)
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hIJ : Ideal.map (algebraMap A B) I = Ideal.map (algebraMap A B) J) :
    ∃ r ∈ M, ∀ (C : Type z) [CommRing C] [Algebra A C],
      IsUnit (algebraMap A C (algebraMap R A r)) →
        Ideal.map (algebraMap A C) I = Ideal.map (algebraMap A C) J := by
  obtain ⟨r, hr, h₁⟩ := exists_localization_map_le M I J hI hIJ.le
  obtain ⟨s, hs, h₂⟩ := exists_localization_map_le M J I hJ hIJ.ge
  refine ⟨r * s, M.mul_mem hr hs, ?_⟩
  intro C _ _ hc
  have hu : IsUnit (algebraMap A C (algebraMap R A r)) ∧
      IsUnit (algebraMap A C (algebraMap R A s)) := by
    apply IsUnit.mul_iff.mp
    simpa only [map_mul] using hc
  exact le_antisymm (h₁ C hu.1) (h₂ C hu.2)

end

end GroupActions
