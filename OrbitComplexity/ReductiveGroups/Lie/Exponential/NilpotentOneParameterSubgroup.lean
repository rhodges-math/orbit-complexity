import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentExponentialConjugation

/-!
# Nilpotent One Parameter Subgroup

A nilpotent element gives a one-parameter subgroup of the ambient unit group. -/

noncomputable section

namespace ReductiveGroups

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

private theorem associativeExponential_add_smul {x : A} (hx : IsNilpotent x)
    (t s : K) :
    associativeExponential (K := K) ((t + s) • x) =
      associativeExponential (K := K) (t • x) *
        associativeExponential (K := K) (s • x) :=
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  by
    rw [add_smul]
    exact IsNilpotent.exp_add_of_commute
      ((Commute.refl x).smul_left t |>.smul_right s)
      (hx.smul t) (hx.smul s)

/-- The unit represented by the finite exponential of `t • x`. -/
def nilpotentExponentialUnit (x : A) (hx : IsNilpotent x) (t : K) : Aˣ where
  val := associativeExponential (K := K) (t • x)
  inv := associativeExponential (K := K) ((-t) • x)
  val_inv := by
    simpa [neg_smul] using
      (associativeExponential_inverse (K := K) (hx.smul t)).1
  inv_val := by
    simpa [neg_smul] using
      (associativeExponential_inverse (K := K) (hx.smul t)).2

/-- The equality is

```lean
(nilpotentExponentialUnit x hx t : A) =
      associativeExponential (K := K) (t • x)
```
-/
@[simp] theorem nilpotentExponentialUnit_val (x : A) (hx : IsNilpotent x) (t : K) :
    (nilpotentExponentialUnit x hx t : A) =
      associativeExponential (K := K) (t • x) := rfl

/-- The equality is

```lean
(((nilpotentExponentialUnit x hx t)⁻¹ : Aˣ) : A) =
      associativeExponential (K := K) ((-t) • x)
```
-/
@[simp] theorem nilpotentExponentialUnit_inv_val (x : A) (hx : IsNilpotent x) (t : K) :
    (((nilpotentExponentialUnit x hx t)⁻¹ : Aˣ) : A) =
      associativeExponential (K := K) ((-t) • x) := rfl

/-- The additive parameter group maps to the ambient unit group by finite exponential. -/
def nilpotentOneParameterSubgroup (x : A) (hx : IsNilpotent x) :
    Multiplicative K →* Aˣ where
  toFun t := nilpotentExponentialUnit x hx (Multiplicative.toAdd t)
  map_one' := by
    apply Units.ext
    change associativeExponential (K := K) ((0 : K) • x) = 1
    simp [associativeExponential]
  map_mul' t s := by
    apply Units.ext
    change associativeExponential (K := K)
      ((Multiplicative.toAdd t + Multiplicative.toAdd s) • x) =
        associativeExponential (K := K) ((Multiplicative.toAdd t) • x) *
          associativeExponential (K := K) ((Multiplicative.toAdd s) • x)
    exact associativeExponential_add_smul hx _ _

/-- The equality is

```lean
(nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd t) : A) =
      associativeExponential (K := K) (t • x)
```
-/
@[simp] theorem nilpotentOneParameterSubgroup_apply (x : A) (hx : IsNilpotent x)
    (t : K) :
    (nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd t) : A) =
      associativeExponential (K := K) (t • x) := rfl

/-- The equality is

```lean
nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd (0 : K)) = 1
```
-/
theorem nilpotentOneParameterSubgroup_zero (x : A) (hx : IsNilpotent x) :
    nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd (0 : K)) = 1 := by
  exact map_one (nilpotentOneParameterSubgroup x hx)

/-- The equality is

```lean
nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd (t + s)) =
      nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd t) *
        nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd s)
```
-/
theorem nilpotentOneParameterSubgroup_add (x : A) (hx : IsNilpotent x)
    (t s : K) :
    nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd (t + s)) =
      nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd t) *
        nilpotentOneParameterSubgroup x hx (Multiplicative.ofAdd s) := by
  exact map_mul (nilpotentOneParameterSubgroup x hx) _ _

end ReductiveGroups
