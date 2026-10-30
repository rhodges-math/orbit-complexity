import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWords
import Mathlib.Algebra.Lie.Solvable

/-!
# Derived Lie Words

Balanced Lie words use the same leaves as balanced group commutators.
Their linear span is exactly the corresponding Lie derived-series term. -/

noncomputable section
namespace ReductiveGroups

/-- The balanced Lie word of depth n, on the same 2^n leaves as the group word. -/
def derivedLieWord {L : Type*} [LieRing L] :
    (n : ℕ) → (DerivedWordIndex n → L) → L
  | 0, x => x PUnit.unit
  | n + 1, x =>
      ⁅derivedLieWord n (fun i => x (false, i)),
        derivedLieWord n (fun i => x (true, i))⁆

/-- The equality is

```lean
derivedLieWord 0 x = x PUnit.unit
```
-/
@[simp] theorem derivedLieWord_zero {L : Type*} [LieRing L]
    (x : DerivedWordIndex 0 → L) : derivedLieWord 0 x = x PUnit.unit := rfl

/-- The equality is

```lean
derivedLieWord (n + 1) x =
      ⁅derivedLieWord n (fun i => x (false, i)),
        derivedLieWord n (fun i => x (true, i))⁆
```
-/
@[simp] theorem derivedLieWord_succ {L : Type*} [LieRing L]
    (n : ℕ) (x : DerivedWordIndex (n + 1) → L) :
    derivedLieWord (n + 1) x =
      ⁅derivedLieWord n (fun i => x (false, i)),
        derivedLieWord n (fun i => x (true, i))⁆ := rfl

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- For these parameters,

```lean
derivedLieWord n x ∈ LieAlgebra.derivedSeries R L n
```
-/
theorem derivedLieWord_mem_derivedSeries (n : ℕ) (x : DerivedWordIndex n → L) :
    derivedLieWord n x ∈ LieAlgebra.derivedSeries R L n := by
  induction n with
  | zero => exact LieSubmodule.mem_top _
  | succ n ih =>
      simpa only [derivedLieWord_succ, LieAlgebra.derivedSeries_def,
        LieAlgebra.derivedSeriesOfIdeal_succ] using
        LieSubmodule.lie_mem_lie
          (ih (fun i => x (false, i))) (ih (fun i => x (true, i)))

private theorem bracket_mem_span_derivedLieWord (n : ℕ)
    (u v : L)
    (hu : u ∈ Submodule.span R (Set.range (derivedLieWord (L := L) n)))
    (hv : v ∈ Submodule.span R (Set.range (derivedLieWord (L := L) n))) :
    ⁅u, v⁆ ∈ Submodule.span R (Set.range (derivedLieWord (L := L) (n + 1))) := by
  let S := Submodule.span R (Set.range (derivedLieWord (L := L) (n + 1)))
  change ⁅u, v⁆ ∈ S
  refine Submodule.span_induction (p := fun u _ => ⁅u, v⁆ ∈ S) ?_ ?_ ?_ ?_ hu
  · rintro u ⟨x, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => ⁅derivedLieWord n x, v⁆ ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro v ⟨y, rfl⟩
      exact Submodule.subset_span ⟨fun i => if i.1 then y i.2 else x i.2, rfl⟩
    · simpa only [lie_zero] using S.zero_mem
    · intro a b _ _ ha hb
      rw [lie_add]
      exact S.add_mem ha hb
    · intro c a _ ha
      rw [lie_smul]
      exact S.smul_mem c ha
  · simpa only [zero_lie] using S.zero_mem
  · intro a b _ _ ha hb
    rw [add_lie]
    exact S.add_mem ha hb
  · intro c a _ ha
    rw [smul_lie]
    exact S.smul_mem c ha

/-- The depth counts derived-series steps, not the number of leaves. -/
theorem span_range_derivedLieWord (n : ℕ) :
    Submodule.span R (Set.range (derivedLieWord (L := L) n)) =
      (LieAlgebra.derivedSeries R L n).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    exact derivedLieWord_mem_derivedSeries n x
  · induction n with
    | zero =>
        intro z _
        exact Submodule.subset_span ⟨fun _ => z, rfl⟩
    | succ n ih =>
        rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
          LieSubmodule.lieIdeal_oper_eq_linear_span']
        apply Submodule.span_le.mpr
        rintro z ⟨u, hu, v, hv, rfl⟩
        exact bracket_mem_span_derivedLieWord n u v (ih hu) (ih hv)

/-- The equality is

```lean
LieAlgebra.derivedSeries R L n = ⊥
```
-/
theorem DerivedSeries.eq_bot_of_derivedLieWord_eq_zero
    (n : ℕ) (hn : ∀ x : DerivedWordIndex n → L, derivedLieWord n x = 0) :
    LieAlgebra.derivedSeries R L n = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  rw [← span_range_derivedLieWord]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro z ⟨x, rfl⟩
  change derivedLieWord n x = 0
  exact hn x

/-- A balanced Lie identity forces solvability of the original
Lie algebra,. -/
theorem lie_isSolvable_of_derivedLieWord_eq_zero
    (n : ℕ) (hn : ∀ x : DerivedWordIndex n → L, derivedLieWord n x = 0) :
    LieAlgebra.IsSolvable L :=
  LieAlgebra.IsSolvable.mk (DerivedSeries.eq_bot_of_derivedLieWord_eq_zero (R := ℤ) n hn)

end ReductiveGroups
