import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.FinTrdeg

/-!
# Equivariant isomorphisms of fixed fields

An equivariant algebra isomorphism restricts to an isomorphism between the intermediate
fields of fixed points. Their transcendence degrees agree.

## Main definitions

* `fixedFieldEquiv`: the restriction of an equivariant algebra isomorphism to fixed fields.

## Main results

* `fixedField_finTrdeg`: the fixed field of an extension of finite transcendence degree
  also has finite transcendence degree.
* `fixedField_trdeg_sub`: the transcendence degree of a fixed field is the difference
  of the ambient and relative transcendence degrees.

## Implementation notes

Fixed fields use `FixedPoints.intermediateField`. The acting object is a monoid.
-/

namespace GroupActions

universe u v w z

variable {K : Type u} [Field K]
variable {M : Type v} [Monoid M]
variable {L : Type w} [Field L] [Algebra K L]
variable {L' : Type z} [Field L'] [Algebra K L']
variable [MulSemiringAction M L] [SMulCommClass M K L]
variable [MulSemiringAction M L'] [SMulCommClass M K L']

/-- An equivariant algebra isomorphism restricts to the intermediate fields of fixed points. -/
def fixedFieldEquiv (e : L ≃ₐ[K] L')
    (hequiv : ∀ (m : M) (x : L), e (m • x) = m • e x) :
    (FixedPoints.intermediateField (F := K) M : IntermediateField K L) ≃ₐ[K]
      (FixedPoints.intermediateField (F := K) M : IntermediateField K L') where
  toFun x := ⟨e x, fun m ↦ by rw [← hequiv, x.property m]⟩
  invFun y := ⟨e.symm y, fun m ↦ e.injective (by
    rw [hequiv, e.apply_symm_apply, y.property m])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)
  map_add' x y := Subtype.ext (e.map_add x y)
  commutes' c := Subtype.ext (e.commutes c)

/-- Natural transcendence degrees add in the tower through a fixed intermediate field. -/
theorem fixedField_trdeg_add [FinTrdeg K L] :
    (Algebra.trdeg K
      (FixedPoints.intermediateField (F := K) M : IntermediateField K L)).toNat +
    (Algebra.trdeg
      (FixedPoints.intermediateField (F := K) M : IntermediateField K L) L).toNat =
    (Algebra.trdeg K L).toNat := by
  have h := trdeg_add_eq K
    (FixedPoints.intermediateField (F := K) M : IntermediateField K L) (A := L)
  have hfinite := (Cardinal.add_lt_aleph0_iff.mp (h ▸ trdeg_lt_aleph0 K L))
  simpa only [Cardinal.toNat_add hfinite.1 hfinite.2] using congrArg Cardinal.toNat h

/-- The natural transcendence degree of a fixed field is the ambient degree minus the
transcendence degree over that fixed field. -/
theorem fixedField_trdeg_sub [FinTrdeg K L] :
    (Algebra.trdeg K
      (FixedPoints.intermediateField (F := K) M : IntermediateField K L)).toNat =
    (Algebra.trdeg K L).toNat -
      (Algebra.trdeg
        (FixedPoints.intermediateField (F := K) M : IntermediateField K L) L).toNat := by
  exact Nat.eq_sub_of_add_eq (fixedField_trdeg_add (K := K) (M := M) (L := L))

end GroupActions
