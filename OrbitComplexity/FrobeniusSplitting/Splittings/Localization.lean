import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Localization of Frobenius splittings

A Frobenius splitting extends uniquely to a localization. Fractions with a
`p`-th-power denominator give an explicit formula for the extension.

## Main definitions

* `FrobeniusSplitting.RingSplitting.localize`: the splitting on a localization.

## Main results

* `FrobeniusSplitting.RingSplitting.localize_mk'`: the value on a fraction with
  `p`-th-power denominator.
* `FrobeniusSplitting.RingSplitting.localize_algebraMap`: commutation with the
  localization map.
* `FrobeniusSplitting.RingSplitting.localize_eq`: uniqueness of the extension.
* `FrobeniusSplitting.RingSplitting.map_localize`: naturality of the extension.

## Implementation notes

The construction uses Mathlib's abstract localization property. Equality of
fraction representatives is checked after clearing denominators, so the base
ring may have zero divisors.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Section 1.1.
-/

namespace FrobeniusSplitting.RingSplitting

open IsLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {p : ℕ} (M : Submonoid R) [IsLocalization M S]

include M

private theorem map_eq_of_map_eq (splitting : RingSplitting R p) (hp : 0 < p)
    {a b : R} (heq : algebraMap R S a = algebraMap R S b) :
    algebraMap R S (splitting a) = algebraMap R S (splitting b) := by
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists M S).1 heq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hpower : (s : R) ^ (n + 1) * a = (s : R) ^ (n + 1) * b := by
    rw [pow_succ, mul_assoc, hs, ← mul_assoc]
  have hsplit := congrArg splitting hpower
  rw [splitting.map_pow_mul, splitting.map_pow_mul] at hsplit
  exact (IsLocalization.eq_iff_exists M S).2 ⟨s, hsplit⟩

private theorem mk'_split_eq (splitting : RingSplitting R p) (hp : 0 < p)
    {a b : R} {s t : M} (heq : mk' S a (s ^ p) = mk' S b (t ^ p)) :
    mk' S (splitting a) s = mk' S (splitting b) t := by
  rw [IsLocalization.mk'_eq_iff_eq] at heq ⊢
  simp only [SubmonoidClass.coe_pow] at heq
  have hsplit := map_eq_of_map_eq M splitting hp heq
  simpa only [splitting.map_pow_mul] using hsplit

private theorem exists_pow_denom (hp : 0 < p) (x : S) :
    ∃ a : R, ∃ s : M, mk' S a (s ^ p) = x := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  refine ⟨a * (s : R) ^ (p - 1), s, ?_⟩
  rw [IsLocalization.mk'_eq_iff_eq']
  simp only [SubmonoidClass.coe_pow]
  congr 1
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]

private noncomputable def localizeMap (splitting : RingSplitting R p) (hp : 0 < p)
    (x : S) : S :=
  mk' S (splitting (Classical.choose (exists_pow_denom M hp x)))
    (Classical.choose (Classical.choose_spec (exists_pow_denom M hp x)))

private theorem localizeMap_mk' (splitting : RingSplitting R p) (hp : 0 < p)
    (a : R) (s : M) :
    localizeMap M splitting hp (mk' S a (s ^ p)) = mk' S (splitting a) s := by
  exact mk'_split_eq M splitting hp
    (Classical.choose_spec (Classical.choose_spec
      (exists_pow_denom M hp (mk' S a (s ^ p)))))

/-- A Frobenius splitting extends to every localization of the ring. -/
noncomputable def localize (splitting : RingSplitting R p) (hp : 0 < p) :
    RingSplitting S p where
  toAddMonoidHom :=
    { toFun := localizeMap M splitting hp
      map_zero' := by
        simpa only [zero_pow (Nat.ne_of_gt hp), mk'_zero, splitting.map_zero] using
          localizeMap_mk' (S := S) M splitting hp 0 1
      map_add' := by
        intro x y
        obtain ⟨a, s, rfl⟩ := exists_pow_denom M hp x
        obtain ⟨b, t, rfl⟩ := exists_pow_denom M hp y
        rw [← mk'_add, ← mul_pow, localizeMap_mk', localizeMap_mk', localizeMap_mk']
        rw [← mk'_add]
        congr 1
        simp only [SubmonoidClass.coe_pow, splitting.map_add]
        rw [mul_comm a, mul_comm b, splitting.map_pow_mul, splitting.map_pow_mul]
        ring
    }
  map_pow_mul' := by
    intro x y
    obtain ⟨a, s, rfl⟩ := exists_pow_denom M hp x
    obtain ⟨b, t, rfl⟩ := exists_pow_denom M hp y
    change localizeMap M splitting hp ((mk' S a (s ^ p)) ^ p * mk' S b (t ^ p)) =
      mk' S a (s ^ p) * localizeMap M splitting hp (mk' S b (t ^ p))
    rw [← mk'_pow, ← mk'_mul, ← mul_pow,
      localizeMap_mk', localizeMap_mk', splitting.map_pow_mul, mk'_mul]
  map_one' := by
    change localizeMap M splitting hp 1 = 1
    simpa only [one_pow, mk'_one, _root_.map_one, splitting.map_one] using
      localizeMap_mk' (S := S) M splitting hp 1 1

/-- The localized splitting replaces a `p`-th-power denominator and splits the numerator. -/
theorem localize_mk' (splitting : RingSplitting R p) (hp : 0 < p) (a : R) (s : M) :
    localize M splitting hp (mk' S a (s ^ p)) = mk' S (splitting a) s :=
  localizeMap_mk' M splitting hp a s

/-- The localized splitting commutes with the localization algebra map. -/
theorem localize_algebraMap (splitting : RingSplitting R p) (hp : 0 < p) (a : R) :
    localize M splitting hp (algebraMap R S a) = algebraMap R S (splitting a) := by
  simpa only [one_pow, mk'_one] using localize_mk' (S := S) M splitting hp a 1

/-- Any splitting commuting with the localization map equals the localized splitting. -/
theorem localize_eq (splitting : RingSplitting R p) (hp : 0 < p)
    (other : RingSplitting S p)
    (hcommute : ∀ a, other (algebraMap R S a) = algebraMap R S (splitting a)) :
    localize M splitting hp = other := by
  ext x
  obtain ⟨a, s, rfl⟩ := exists_pow_denom M hp x
  rw [localize_mk']
  apply (IsLocalization.map_units S s).mul_right_inj.1
  rw [mk'_spec']
  have hsplit := congrArg other (mk'_spec' S a (s ^ p))
  rw [SubmonoidClass.coe_pow, (algebraMap R S).map_pow, other.map_pow_mul,
    hcommute] at hsplit
  exact hsplit.symm

/-- Commutation with a splitting extends from a ring to a localization. -/
theorem map_localize {T : Type*} [CommRing T] (splitting : RingSplitting R p)
    (hp : 0 < p) (target : RingSplitting T p) (morphism : S →+* T)
    (hcommute : ∀ a, target (morphism (algebraMap R S a)) =
      morphism (algebraMap R S (splitting a))) (x : S) :
    target (morphism x) = morphism (splitting.localize M hp x) := by
  obtain ⟨a, s, rfl⟩ := exists_pow_denom M hp x
  rw [localize_mk']
  apply ((IsLocalization.map_units S s).map morphism).mul_right_inj.1
  have hsplit := congrArg target (congrArg morphism (mk'_spec' S a (s ^ p)))
  simp only [morphism.map_mul, SubmonoidClass.coe_pow, (algebraMap R S).map_pow,
    morphism.map_pow] at hsplit
  rw [target.map_pow_mul, hcommute] at hsplit
  calc
    morphism (algebraMap R S (s : R)) * target (morphism (mk' S a (s ^ p))) =
        morphism (algebraMap R S (splitting a)) := hsplit
    _ = morphism (algebraMap R S (s : R)) * morphism (mk' S (splitting a) s) := by
      rw [← morphism.map_mul, mk'_spec']

end FrobeniusSplitting.RingSplitting
