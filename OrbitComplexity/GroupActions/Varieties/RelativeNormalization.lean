import Mathlib.RingTheory.Localization.Integral

/-! # Clearing integrality denominators

Finitely many elements integral after localizing both the base ring and its algebra have a
common denominator whose multiples are integral in the original algebra. This is the
denominator-clearing step for spreading finite integral maps over an open part of a base.

## Main results

* `GroupActions.exists_common_integral_multiple`: one denominator clears all the integrality
  witnesses in a finite family.
* `GroupActions.integral_after_away`: inverting an integral multiple's scalar makes the
  original element integral over the localized base.
* `GroupActions.integral_localization_of_images`: integral images generate an integral
  localization when its denominators come from the localized base.
* `GroupActions.exists_integral_away`: an integral localization of a finite-type algebra
  spreads to an integral map after inverting one element of the base.
-/

namespace GroupActions

universe u v w z

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private theorem integral_of_unit_smul {r : R} {x : A} (hr : IsUnit r)
    (hx : IsIntegral R (r • x)) : IsIntegral R x := by
  obtain ⟨u, rfl⟩ := hr
  have h := IsIntegral.smul ((u⁻¹ : Rˣ) : R) hx
  simpa only [smul_smul, Units.inv_mul, one_smul] using h

private theorem common_integral_multiple (M : Submonoid R) (t : Finset A)
    (h : ∀ x ∈ t, ∃ m : M, IsIntegral R ((m : R) • x)) :
    ∃ m : M, ∀ x ∈ t, IsIntegral R ((m : R) • x) := by
  classical
  revert h
  induction t using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩
  | @insert x t _ ih =>
    intro h
    obtain ⟨a, ha⟩ := h x (Finset.mem_insert_self _ _)
    obtain ⟨b, hb⟩ := ih (fun y hy ↦ h y (Finset.mem_insert_of_mem hy))
    refine ⟨a * b, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · change IsIntegral R (((a : R) * (b : R)) • y)
      rw [mul_comm, mul_smul]
      exact IsIntegral.smul (b : R) ha
    · change IsIntegral R (((a : R) * (b : R)) • y)
      rw [mul_smul]
      exact IsIntegral.smul (a : R) (hb y hy)

variable {Rₘ : Type w} {Aₘ : Type z} [CommRing Rₘ] [CommRing Aₘ]
  [Algebra R Rₘ] [Algebra A Aₘ] [Algebra R Aₘ] [Algebra Rₘ Aₘ]
  [IsScalarTower R A Aₘ] [IsScalarTower R Rₘ Aₘ]

private theorem integral_images_of_adjoin (t : Finset A)
    (ht : Algebra.adjoin R (t : Set A) = ⊤)
    (h : ∀ x ∈ t, IsIntegral Rₘ (algebraMap A Aₘ x)) :
    ∀ x : A, IsIntegral Rₘ (algebraMap A Aₘ x) := by
  let B : Subalgebra R A :=
    ((integralClosure Rₘ Aₘ).restrictScalars R).comap (IsScalarTower.toAlgHom R A Aₘ)
  have hb : Algebra.adjoin R (t : Set A) ≤ B := Algebra.adjoin_le fun x hx ↦ h x hx
  rw [ht] at hb
  exact fun x ↦ hb (show x ∈ (⊤ : Subalgebra R A) from trivial)

private theorem integral_multiple (M : Submonoid R) [IsLocalization M Rₘ]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) Aₘ] {x : A}
    (hx : IsIntegral Rₘ (algebraMap A Aₘ x)) :
    ∃ m : M, IsIntegral R ((m : R) • x) := by
  obtain ⟨a, ha⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hx
  have ha' : IsIntegral R (algebraMap A Aₘ ((a : R) • x)) := by
    simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply R A Aₘ] using ha
  obtain ⟨b, hb, hbx⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map M ha'
  refine ⟨⟨b, hb⟩ * a, ?_⟩
  change IsIntegral R ((b * (a : R)) • x)
  rw [mul_smul]
  exact hbx

/-- One denominator makes every member of a finite localized integral family integral. -/
theorem exists_common_integral_multiple (M : Submonoid R) [IsLocalization M Rₘ]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) Aₘ] (t : Finset A)
    (h : ∀ x ∈ t, IsIntegral Rₘ (algebraMap A Aₘ x)) :
    ∃ m : M, ∀ x ∈ t, IsIntegral R ((m : R) • x) :=
  common_integral_multiple M t fun x hx ↦ integral_multiple M (h x hx)

/-- Inverting the scalar of an integral multiple makes the element integral over the new base. -/
theorem integral_after_away {r : R} [IsLocalization.Away r Rₘ] {x : A}
    (hx : IsIntegral R (r • x)) : IsIntegral Rₘ (algebraMap A Aₘ x) := by
  apply integral_of_unit_smul (IsLocalization.Away.algebraMap_isUnit (S := Rₘ) r)
  have hx' := IsIntegral.tower_top (A := Rₘ) (hx.algebraMap (B := Aₘ))
  simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A Aₘ,
    ← IsScalarTower.algebraMap_apply R Rₘ Aₘ] using hx'

/-- A localization is integral over the localized base if all original images are integral. -/
theorem integral_localization_of_images {r : R} [IsLocalization.Away r Rₘ]
    [IsLocalization.Away (algebraMap R A r) Aₘ]
    (h : ∀ x : A, IsIntegral Rₘ (algebraMap A Aₘ x)) : Algebra.IsIntegral Rₘ Aₘ := by
  constructor
  intro y
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap R A r) y
  apply integral_of_unit_smul ((IsLocalization.Away.algebraMap_isUnit (S := Rₘ) r).pow n)
  have he : (algebraMap R Rₘ r) ^ n • y = algebraMap A Aₘ a := by
    simpa only [Algebra.smul_def, map_pow, ← IsScalarTower.algebraMap_apply R A Aₘ,
      ← IsScalarTower.algebraMap_apply R Rₘ Aₘ, mul_comm] using ha
  rw [he]
  exact h a

/-- Integrality of a localized finite-type algebra spreads after inverting one base element. -/
theorem exists_integral_away (M : Submonoid R) [Algebra.FiniteType R A]
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid A M) Aₘ]
    [Algebra.IsIntegral Rₘ Aₘ] :
    ∃ m : M, (Localization.awayMap (algebraMap R A) (m : R)).IsIntegral := by
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := A)
  obtain ⟨m, hm⟩ := exists_common_integral_multiple (Rₘ := Rₘ) (Aₘ := Aₘ) M t
    (fun x _ ↦ Algebra.IsIntegral.isIntegral (algebraMap A Aₘ x))
  refine ⟨m, ?_⟩
  let R' := Localization.Away (m : R)
  let A' := Localization.Away (algebraMap R A (m : R))
  let := (Localization.awayMap (algebraMap R A) (m : R)).toAlgebra
  have : IsScalarTower R R' A' :=
    .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  change (algebraMap R' A').IsIntegral
  rw [algebraMap_isIntegral_iff]
  apply integral_localization_of_images (R := R) (A := A) (r := (m : R))
  apply integral_images_of_adjoin t ht
  exact fun x hx ↦ integral_after_away (hm x hx)

end GroupActions
