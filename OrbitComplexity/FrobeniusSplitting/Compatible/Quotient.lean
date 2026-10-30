import OrbitComplexity.FrobeniusSplitting.Compatible.Ideals

/-!
# Splittings of quotient rings

A Frobenius splitting preserving an ideal descends to the quotient by that ideal.
The quotient map commutes with the two splittings.

## Main definitions

* `FrobeniusSplitting.RingSplitting.quotient`: the splitting of a quotient ring.

## Main results

* `FrobeniusSplitting.RingSplitting.quotient_mk`: evaluation on a residue class.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Remark 1.1.4(ii).
-/

namespace FrobeniusSplitting.RingSplitting

variable {R : Type*} [CommRing R] {p : ℕ}

/-- A splitting preserving an ideal induces a splitting of the quotient ring. -/
def quotient (splitting : RingSplitting R p) (ideal : Ideal R)
    (hcompatible : splitting.IsCompatible ideal) : RingSplitting (R ⧸ ideal) p where
  toAddMonoidHom := QuotientAddGroup.lift ideal.toAddSubgroup
    ((Ideal.Quotient.mk ideal).toAddMonoidHom.comp splitting.toAddMonoidHom)
    (fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.2 (hcompatible ha))
  map_pow_mul' a b := by
    refine Quotient.inductionOn₂' a b ?_
    intro a b
    change Ideal.Quotient.mk ideal (splitting (a ^ p * b)) =
      Ideal.Quotient.mk ideal a * Ideal.Quotient.mk ideal (splitting b)
    rw [splitting.map_pow_mul, map_mul]
  map_one' := by
    change Ideal.Quotient.mk ideal (splitting 1) = 1
    rw [splitting.map_one, (Ideal.Quotient.mk ideal).map_one]

/-- Applying the quotient splitting to a residue class gives the class of its splitting. -/
@[simp]
theorem quotient_mk (splitting : RingSplitting R p) (ideal : Ideal R)
    (hcompatible : splitting.IsCompatible ideal) (a : R) :
    splitting.quotient ideal hcompatible (Ideal.Quotient.mk ideal a) =
      Ideal.Quotient.mk ideal (splitting a) :=
  rfl

end FrobeniusSplitting.RingSplitting
