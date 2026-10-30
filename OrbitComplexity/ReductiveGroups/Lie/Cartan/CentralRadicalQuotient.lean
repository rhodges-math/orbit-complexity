import OrbitComplexity.ReductiveGroups.Lie.Roots.RadicalQuotient
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Extension

/-!
# Central Radical Quotient

The center quotient of a finite-dimensional reductive Lie algebra:
Killing on the quotient and a central extension with middle exactly the
original Lie algebra.  -/

noncomputable section
namespace ReductiveGroups

variable {K L : Type*} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.Finite K L]

/-- For these parameters,

```lean
LieAlgebra.IsKilling K (L ⧸ LieAlgebra.center K L)
```
-/
theorem centralRadical_centerQuotient_isKilling
    [LieAlgebra.HasCentralRadical K L] :
    LieAlgebra.IsKilling K (L ⧸ LieAlgebra.center K L) := by
  have h : LieAlgebra.HasTrivialRadical K
      (L ⧸ LieAlgebra.center K L) := by
    have heq : LieAlgebra.radical K L = LieAlgebra.center K L :=
      LieAlgebra.radical_eq_center
    rw [← heq]
    exact hasTrivialRadical_quotient_radical (K := K) (L := L)
  let _ : LieAlgebra.HasTrivialRadical K (L ⧸ LieAlgebra.center K L) := h
  infer_instance

/-- The quotient map to the center quotient, as a Lie homomorphism. -/
def centerQuotientLieHom : L →ₗ⁅K⁆ (L ⧸ LieAlgebra.center K L) where
  toLinearMap := (LieSubmodule.Quotient.mk'
    (LieAlgebra.center K L)).toLinearMap
  map_lie' := by intros; rfl

omit [CharZero K] [Module.Finite K L] in
/-- The equality is

```lean
centerQuotientLieHom (K := K) x =
      (LieSubmodule.Quotient.mk' (LieAlgebra.center K L)) x
```
-/
@[simp] theorem centerQuotientLieHom_apply (x : L) :
    centerQuotientLieHom (K := K) x =
      (LieSubmodule.Quotient.mk' (LieAlgebra.center K L)) x := rfl

omit [CharZero K] [Module.Finite K L] in
/-- The equality is

```lean
Function.Surjective (centerQuotientLieHom (K := K) (L := L))
```
-/
theorem centerQuotientLieHom_surjective :
    Function.Surjective (centerQuotientLieHom (K := K) (L := L)) :=
  LieSubmodule.Quotient.surjective_mk' _

omit [CharZero K] [Module.Finite K L] in
/-- The equality is

```lean
(centerQuotientLieHom (K := K) (L := L)).ker =
      LieAlgebra.center K L
```
-/
@[simp] theorem centerQuotientLieHom_ker :
    (centerQuotientLieHom (K := K) (L := L)).ker =
      LieAlgebra.center K L := by
  ext x
  change (LieSubmodule.Quotient.mk' (LieAlgebra.center K L)) x = 0 ↔
    x ∈ LieAlgebra.center K L
  exact LieSubmodule.Quotient.mk_eq_zero (N := LieAlgebra.center K L) (m := x)

/-- The exact central extension with middle object definitionally `L`:
`0 → center(L) → L → L/center(L) → 0`. -/
def centerLieExtension : LieAlgebra.Extension K
    (LieAlgebra.center K L) (L ⧸ LieAlgebra.center K L) where
  L := L
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl := (LieAlgebra.center K L).incl
  proj := centerQuotientLieHom
  IsExtension := {
    ker_eq_bot := LieIdeal.ker_incl _
    range_eq_top := (LieHom.range_eq_top _).mpr centerQuotientLieHom_surjective
    exact := by rw [LieIdeal.incl_range, centerQuotientLieHom_ker] }

omit [CharZero K] [Module.Finite K L] in
/-- The equality is

```lean
(centerLieExtension (K := K) (L := L)).incl z = (z : L)
```
-/
@[simp] theorem centerLieExtension_incl (z : LieAlgebra.center K L) :
    (centerLieExtension (K := K) (L := L)).incl z = (z : L) := rfl

omit [CharZero K] [Module.Finite K L] in
/-- The equality is

```lean
(centerLieExtension (K := K) (L := L)).proj x =
      centerQuotientLieHom (K := K) x
```
-/
@[simp] theorem centerLieExtension_proj (x : L) :
    (centerLieExtension (K := K) (L := L)).proj x =
      centerQuotientLieHom (K := K) x := rfl

omit [CharZero K] [Module.Finite K L] in
/-- The kernel inclusion is central in the original Lie algebra. -/
theorem centerLieExtension_central (x : L) (z : LieAlgebra.center K L) :
    ⁅x, (z : L)⁆ = 0 := by
  exact (LieModule.mem_maxTrivSubmodule (R := K) (L := L) (M := L) z).mp z.property x

omit [CharZero K] [Module.Finite K L] in
/-- The equality is

```lean
⁅x, (centerLieExtension (K := K) (L := L)).incl z⁆ = 0
```
-/
theorem centerLieExtension_incl_central
    (x : (centerLieExtension (K := K) (L := L)).L)
    (z : LieAlgebra.center K L) :
    ⁅x, (centerLieExtension (K := K) (L := L)).incl z⁆ = 0 := by
  dsimp [centerLieExtension] at x ⊢
  change ⁅x, (z : L)⁆ = 0
  exact centerLieExtension_central (K := K) (L := L) x z

end ReductiveGroups
