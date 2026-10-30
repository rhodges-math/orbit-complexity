import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import OrbitComplexity.FrobeniusSplitting.Splittings.Transport
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# Frobenius splittings of group algebras

A coefficient splitting extends to an additive group algebra by dividing
exponents by the characteristic. Multiplication by the characteristic must be
injective on the exponent group. The construction commutes with group
isomorphisms and therefore with changes of lattice basis.

## Main definitions

* `FrobeniusSplitting.RingSplitting.addMonoidAlgebra`: the group algebra splitting.

## Main results

* `FrobeniusSplitting.RingSplitting.addMonoidAlgebra_coeff`: its coefficient formula.
* `FrobeniusSplitting.RingSplitting.addMonoidAlgebra_transport`: invariance under transport.
-/

namespace FrobeniusSplitting.RingSplitting

open AddMonoidAlgebra

variable {R G H : Type*} [CommSemiring R] [AddCommGroup G] {p : ℕ}

private noncomputable def groupMap (base : RingSplitting R p)
    (hscale : Function.Injective (fun a : G ↦ p • a)) :
    AddMonoidAlgebra R G →+ AddMonoidAlgebra R G where
  toFun f := ofCoeff (Finsupp.mapRange base base.map_zero
    (Finsupp.comapDomain (fun a : G ↦ p • a) f.coeff hscale.injOn))
  map_zero' := by
    ext d
    exact base.map_zero
  map_add' f g := by
    ext d
    exact base.map_add (f.coeff (p • d)) (g.coeff (p • d))

private theorem groupMap_coeff (base : RingSplitting R p)
    (hscale : Function.Injective (fun a : G ↦ p • a))
    (f : AddMonoidAlgebra R G) (d : G) :
    (groupMap base hscale f).coeff d = base (f.coeff (p • d)) := rfl

private theorem groupMap_single (base : RingSplitting R p)
    (hscale : Function.Injective (fun a : G ↦ p • a))
    (a : G) (r : R) (g : AddMonoidAlgebra R G) :
    groupMap base hscale ((single a r) ^ p * g) = single a r * groupMap base hscale g := by
  ext d
  rw [groupMap_coeff, single_pow, coeff_single_mul_apply, coeff_single_mul_apply]
  rw [← smul_neg, ← smul_add, base.map_pow_mul, groupMap_coeff]

/-- A coefficient splitting and division of group exponents split the additive group algebra. -/
noncomputable def addMonoidAlgebra [ExpChar R p] (base : RingSplitting R p)
    (hscale : Function.Injective (fun a : G ↦ p • a)) :
    RingSplitting (AddMonoidAlgebra R G) p where
  toAddMonoidHom := groupMap base hscale
  map_pow_mul' a b := by
    have : ExpChar (AddMonoidAlgebra R G) p :=
      expChar_of_injective_ringHom
        (f := AddMonoidAlgebra.singleZeroRingHom (R := R) (M := G))
        single_right_injective p
    change groupMap base hscale (a ^ p * b) = a * groupMap base hscale b
    refine Finsupp.induction_linear (motive := fun f : G →₀ R ↦
      groupMap base hscale ((ofCoeff f) ^ p * b) = ofCoeff f * groupMap base hscale b)
      a.coeff ?_ ?_ ?_
    · simp only [ofCoeff_zero, zero_pow (expChar_ne_zero R p), zero_mul,
        (groupMap base hscale).map_zero]
    · intro f g hf hg
      change groupMap base hscale (((ofCoeff f) + ofCoeff g) ^ p * b) = _
      rw [add_pow_expChar, add_mul, (groupMap base hscale).map_add, hf, hg,
        ofCoeff_add, add_mul]
    · intro a r
      exact groupMap_single base hscale a r b
  map_one' := by
    classical
    ext d
    rw [groupMap_coeff]
    by_cases hd : d = 0
    · subst d
      simp only [smul_zero, coeff_one_zero]
      exact base.map_one
    · have hpd : p • d ≠ 0 := by
        intro hzero
        apply hd
        apply hscale
        simpa only [smul_zero] using hzero
      simp only [one_def, coeff_single, Finsupp.single_apply,
        ite_eq_right (Ne.symm hd), ite_eq_right (Ne.symm hpd), base.map_zero]

/-- The group algebra splitting extracts coefficients at exponents divisible
by the characteristic. -/
theorem addMonoidAlgebra_coeff [ExpChar R p] (base : RingSplitting R p)
    (hscale : Function.Injective (fun a : G ↦ p • a))
    (f : AddMonoidAlgebra R G) (d : G) :
    (base.addMonoidAlgebra hscale f).coeff d = base (f.coeff (p • d)) := rfl

/-- An isomorphism of exponent groups commutes with the group algebra splitting. -/
theorem addMonoidAlgebra_naturality [AddCommGroup H] [ExpChar R p]
    (base : RingSplitting R p) (hG : Function.Injective (fun a : G ↦ p • a))
    (hH : Function.Injective (fun a : H ↦ p • a)) (e : G ≃+ H)
    (f : AddMonoidAlgebra R G) :
    base.addMonoidAlgebra hH (AddMonoidAlgebra.mapDomainRingEquiv R e f) =
      AddMonoidAlgebra.mapDomainRingEquiv R e (base.addMonoidAlgebra hG f) := by
  ext d
  rw [addMonoidAlgebra_coeff, coeff_mapDomainRingEquiv, coeff_mapDomainRingEquiv]
  simp only [Finsupp.equivMapDomain_apply, addMonoidAlgebra_coeff]
  change base (f.coeff (e.symm (p • d))) = base (f.coeff (p • e.symm d))
  rw [_root_.map_nsmul]

/-- Transport under an exponent-group isomorphism preserves the canonical splitting. -/
theorem addMonoidAlgebra_transport [AddCommGroup H] [ExpChar R p]
    (base : RingSplitting R p) (hG : Function.Injective (fun a : G ↦ p • a))
    (hH : Function.Injective (fun a : H ↦ p • a)) (e : G ≃+ H) :
    (base.addMonoidAlgebra hG).transport (AddMonoidAlgebra.mapDomainRingEquiv R e) =
      base.addMonoidAlgebra hH := by
  apply RingSplitting.ext
  intro f
  have h := base.addMonoidAlgebra_naturality hG hH e
    ((AddMonoidAlgebra.mapDomainRingEquiv R e).symm f)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

end FrobeniusSplitting.RingSplitting
