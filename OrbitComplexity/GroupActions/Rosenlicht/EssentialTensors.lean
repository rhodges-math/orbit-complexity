import OrbitComplexity.GroupActions.Rosenlicht.TensorDomains
import OrbitComplexity.GroupActions.Rosenlicht.GenericFieldFibres
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Scalar extension of finitely generated fields

A field essentially of finite type is the fraction field of a finite-type
integral algebra. Over an algebraically closed base, the scalar extension of
this algebra and its fraction field to any integral algebra stays integral.
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w

private theorem essFiniteType_fractionRing (k : Type u) [Field k]
    (F : Type v) [Field F] [Algebra k F] [Algebra.EssFiniteType k F] :
    IsFractionRing (Algebra.EssFiniteType.subalgebra k F) F := by
  have hs : Algebra.EssFiniteType.submonoid k F =
      nonZeroDivisors (Algebra.EssFiniteType.subalgebra k F) := by
    ext a
    simp only [Algebra.EssFiniteType.submonoid, Submonoid.mem_comap,
      IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    change (a : F) ≠ 0 ↔ a ≠ 0
    exact Subtype.val_injective.ne_iff (x := a) (y := 0)
  change IsLocalization (nonZeroDivisors (Algebra.EssFiniteType.subalgebra k F)) F
  rw [← hs]
  infer_instance

/-- A field essentially of finite type over an algebraically closed field stays
integral after tensoring with an integral algebra. -/
theorem tensorField_isDomain (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (B : Type w) [CommRing B] [Algebra k B] [IsDomain B] : IsDomain (F ⊗[k] B) := by
  let A := Algebra.EssFiniteType.subalgebra k F
  have : IsFractionRing A F := essFiniteType_fractionRing k F
  have : IsDomain (A ⊗[k] B) := isDomain_tensorProduct
  exact tensorFraction_isDomain k A F B

end

end GroupActions
