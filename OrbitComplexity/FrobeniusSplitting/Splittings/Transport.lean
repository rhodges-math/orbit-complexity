import OrbitComplexity.FrobeniusSplitting.Splittings.Basic

/-!
# Transport of Frobenius splittings

Ring isomorphisms carry Frobenius-linear retractions to Frobenius-linear
retractions. This identifies splittings across isomorphic rings of sections.

## Main definitions

* `FrobeniusSplitting.RingSplitting.transport`: transport along a ring isomorphism.

## Main results

* `FrobeniusSplitting.RingSplitting.transport_apply`: the formula for transport.
* `FrobeniusSplitting.RingSplitting.transport_trans`: compatibility with composition.
-/

namespace FrobeniusSplitting.RingSplitting

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] {p : ℕ}

/-- A ring isomorphism carries a splitting to a splitting of its target. -/
def transport (splitting : RingSplitting R p) (equiv : R ≃+* S) : RingSplitting S p where
  toAddMonoidHom := equiv.toAddMonoidHom.comp
    (splitting.toAddMonoidHom.comp equiv.symm.toAddMonoidHom)
  map_pow_mul' a b := by
    change equiv (splitting (equiv.symm (a ^ p * b))) =
      a * equiv (splitting (equiv.symm b))
    rw [equiv.symm.map_mul, equiv.symm.map_pow, splitting.map_pow_mul,
      equiv.map_mul, equiv.apply_symm_apply]
  map_one' := by
    change equiv (splitting (equiv.symm 1)) = 1
    rw [equiv.symm.map_one, splitting.map_one, equiv.map_one]

/-- Transport is conjugation by the ring isomorphism. -/
theorem transport_apply (splitting : RingSplitting R p) (equiv : R ≃+* S) (a : S) :
    splitting.transport equiv a = equiv (splitting (equiv.symm a)) :=
  rfl

/-- Transport along successive ring isomorphisms agrees with transport along their composite. -/
theorem transport_trans (splitting : RingSplitting R p) (equiv : R ≃+* S)
    (other : S ≃+* T) :
    (splitting.transport equiv).transport other = splitting.transport (equiv.trans other) := by
  ext a
  rfl

end FrobeniusSplitting.RingSplitting
