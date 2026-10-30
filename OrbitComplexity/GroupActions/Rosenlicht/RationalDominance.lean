import Mathlib.AlgebraicGeometry.Birational.Dominant
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Dominance detected at the generic point

A rational map from an irreducible scheme is dominant whenever its restriction
to the spectrum of the function field is dominant.

## Main results

* `rationalMap_dominant_of_generic`: generic dominance implies rational dominance.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

universe u

variable {X Y : Scheme.{u}} [IrreducibleSpace X]

/-- A rational map is dominant if its generic restriction is dominant. -/
theorem rationalMap_dominant_of_generic (f : X ⤏ Y) [IsDominant f.fromFunctionField] :
    f.IsDominant := by
  obtain ⟨p, rfl⟩ := f.exists_rep
  have hη : genericPoint X ∈ p.domain :=
    ((genericPoint_spec X).mem_open_set_iff p.domain.isOpen).mpr
      (by simpa using p.dense_domain.nonempty)
  have : IsDominant (p.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ p.hom) :=
    inferInstanceAs (IsDominant p.toRationalMap.fromFunctionField)
  have : IsDominant p.hom :=
    IsDominant.of_comp (p.domain.fromSpecStalkOfMem (genericPoint X) hη) p.hom
  infer_instance

end GroupActions
