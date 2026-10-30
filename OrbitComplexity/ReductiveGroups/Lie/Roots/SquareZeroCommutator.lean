import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Square Zero Commutator

The exact associative-ring calculation for commutators of
infinitesimal elements with disjoint square-zero parameters. -/

namespace ReductiveGroups
open scoped commutatorElement

variable {A : Type*} [Ring A]

/-- The unit 1+u, with inverse 1-u, when u squared is zero. -/
def squareZeroUnit (u : A) (hu : u * u = 0) : Aˣ where
  val := 1 + u
  inv := 1 - u
  val_inv := by
    simp only [mul_sub, add_mul, mul_one, one_mul, hu, add_zero]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, mul_one, one_mul, hu]
    abel

/-- The equality is

```lean
(squareZeroUnit u hu : A) = 1 + u
```
-/
@[simp] theorem squareZeroUnit_val (u : A) (hu : u * u = 0) :
    (squareZeroUnit u hu : A) = 1 + u := rfl

/-- The equality is

```lean
(((squareZeroUnit u hu)⁻¹ : Aˣ) : A) = 1 - u
```
-/
@[simp] theorem squareZeroUnit_inv_val (u : A) (hu : u * u = 0) :
    (((squareZeroUnit u hu)⁻¹ : Aˣ) : A) = 1 - u := rfl

/-- The additional mixed-cubic hypotheses follow for disjoint square-zero
parameter blocks. Square-zero of u and v alone would not suffice. -/
theorem squareZeroUnit_commutator_val
    (u v : A) (hu : u * u = 0) (hv : v * v = 0)
    (huvu : u * v * u = 0) (hvuv : v * u * v = 0) :
    ((⁅squareZeroUnit u hu, squareZeroUnit v hv⁆ : Aˣ) : A) =
      1 + (u * v - v * u) := by
  change (1 + u) * (1 + v) * (1 - u) * (1 - v) = 1 + (u * v - v * u)
  calc
    _ = 1 + (u * v - v * u) - u * u - v * v - u * v * u -
        u * (v * v) + (u * u) * v + v * u * v + (u * v * u) * v := by
          noncomm_ring
    _ = _ := by rw [hu, hv, huvu, hvuv]; simp

end ReductiveGroups
