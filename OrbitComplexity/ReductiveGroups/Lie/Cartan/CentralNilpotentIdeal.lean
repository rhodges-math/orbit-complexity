import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Central Nilpotent Ideal

Central elements acting nilpotently in an associative representation
form a Lie ideal. Centrality is essential for closure under addition. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L A : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [Ring A] [Algebra K A]

/-- The nilpotent central directions in a fixed associative representation. -/
def centralNilpotentIdeal (f : L →ₗ⁅K⁆ A) : LieIdeal K L where
  carrier := {x | x ∈ LieAlgebra.center K L ∧ IsNilpotent (f x)}
  zero_mem' := ⟨(LieAlgebra.center K L).zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(LieAlgebra.center K L).add_mem hx.1 hy.1, ?_⟩
    rw [map_add]
    have hc : Commute (f x) (f y) := by
      rw [Commute.symm_iff, commute_iff_lie_eq, ← LieHom.map_lie, hx.1 y, map_zero]
    exact hc.isNilpotent_add hx.2 hy.2
  smul_mem' := by
    intro r x hx
    refine ⟨(LieAlgebra.center K L).smul_mem r hx.1, ?_⟩
    rw [map_smul]
    exact hx.2.smul r
  lie_mem := by
    intro x y hy
    rw [hy.1 x]
    exact ⟨(LieAlgebra.center K L).zero_mem, by simp⟩

/-- The equivalence is

```lean
x ∈ centralNilpotentIdeal f ↔
      x ∈ LieAlgebra.center K L ∧ IsNilpotent (f x)
```
-/
theorem mem_centralNilpotentIdeal (f : L →ₗ⁅K⁆ A) (x : L) :
    x ∈ centralNilpotentIdeal f ↔
      x ∈ LieAlgebra.center K L ∧ IsNilpotent (f x) := Iff.rfl

/-- The inclusion is

```lean
centralNilpotentIdeal f ≤ LieAlgebra.center K L
```
-/
theorem centralNilpotentIdeal_le_center (f : L →ₗ⁅K⁆ A) :
    centralNilpotentIdeal f ≤ LieAlgebra.center K L := fun _ hx => hx.1

/-- All represented elements of this ideal commute, not merely individually
act nilpotently. -/
theorem centralNilpotentIdeal_images_commute (f : L →ₗ⁅K⁆ A)
    (x y : centralNilpotentIdeal f) : Commute (f (x : L)) (f (y : L)) := by
  rw [Commute.symm_iff, commute_iff_lie_eq, ← LieHom.map_lie, x.property.1 y, map_zero]

/-- The ideal itself is abelian; its embedding retains the full ambient
Lie algebra's center, rather than replacing that algebra by a quotient. -/
theorem centralNilpotentIdeal_isLieAbelian (f : L →ₗ⁅K⁆ A) :
    IsLieAbelian (centralNilpotentIdeal f) :=
  LieAlgebra.abelian_of_le_center K L _ (centralNilpotentIdeal_le_center f)

end ReductiveGroups
