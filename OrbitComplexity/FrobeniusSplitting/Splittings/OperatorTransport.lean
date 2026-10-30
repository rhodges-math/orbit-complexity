import OrbitComplexity.FrobeniusSplitting.Splittings.SheafOperators

/-!
# Transport and restriction of Frobenius-linear operators

Ring isomorphisms transport Frobenius-linear operators by conjugation. Multiplication of an
operator's argument by a weight commutes with that transport. Structure-sheaf operators also
restrict to open subschemes and are determined by their formulas on sections.
-/

namespace FrobeniusSplitting.FrobeniusLinearMap

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] {p : ℕ}

/-- Frobenius-linear operators agreeing at every element are equal. -/
@[ext]
theorem ext {φ ψ : FrobeniusLinearMap R p} (h : ∀ a, φ a = ψ a) : φ = ψ := by
  cases φ with
  | mk f hf =>
    cases ψ with
    | mk g hg =>
      have : f = g := AddMonoidHom.ext h
      subst g
      rfl

/-- A ring isomorphism carries a Frobenius-linear operator to its target. -/
def transport (φ : FrobeniusLinearMap R p) (e : R ≃+* S) : FrobeniusLinearMap S p where
  toAddMonoidHom := e.toAddMonoidHom.comp (φ.toAddMonoidHom.comp e.symm.toAddMonoidHom)
  map_pow_mul' a b := by
    change e (φ (e.symm (a ^ p * b))) = a * e (φ (e.symm b))
    rw [e.symm.map_mul, e.symm.map_pow, φ.map_pow_mul, e.map_mul, e.apply_symm_apply]

/-- Transport conjugates an operator by its ring isomorphism. -/
theorem transport_apply (φ : FrobeniusLinearMap R p) (e : R ≃+* S) (a : S) :
    φ.transport e a = e (φ (e.symm a)) := rfl

/-- Successive changes of ring compose as conjugations. -/
theorem transport_trans (φ : FrobeniusLinearMap R p) (e : R ≃+* S) (f : S ≃+* T) :
    (φ.transport e).transport f = φ.transport (e.trans f) := by
  ext a
  rfl

/-- Multiplying the argument by a fixed weight preserves Frobenius linearity. -/
def weight (φ : FrobeniusLinearMap R p) (c : R) : FrobeniusLinearMap R p where
  toAddMonoidHom :=
    { toFun := fun a ↦ φ (c * a)
      map_zero' := by rw [mul_zero, φ.map_zero]
      map_add' a b := by rw [mul_add, φ.map_add] }
  map_pow_mul' a b := by
    change φ (c * (a ^ p * b)) = a * φ (c * b)
    rw [← mul_assoc, mul_comm c (a ^ p), mul_assoc, φ.map_pow_mul]

/-- A weighted operator multiplies the input by its weight. -/
theorem weight_apply (φ : FrobeniusLinearMap R p) (c a : R) :
    φ.weight c a = φ (c * a) := rfl

/-- Multiplication of weights commutes with transport along ring isomorphisms. -/
theorem weight_transport (φ : FrobeniusLinearMap R p) (e : R ≃+* S) (c : R) :
    (φ.weight c).transport e = (φ.transport e).weight (e c) := by
  ext a
  simp only [transport_apply, weight_apply, e.symm.map_mul, e.symm_apply_apply]

end FrobeniusSplitting.FrobeniusLinearMap

namespace FrobeniusSplitting.SchemeFrobeniusMap

open AlgebraicGeometry CategoryTheory Opposite

variable {X : Scheme} {p : ℕ}

/-- Structure-sheaf operators are determined by their section formulas. -/
@[ext]
theorem ext {φ ψ : SchemeFrobeniusMap X p}
    (h : ∀ U s, φ.onOpen U s = ψ.onOpen U s) : φ = ψ := by
  cases φ with
  | mk f hf =>
    cases ψ with
    | mk g hg =>
      have : f = g := funext fun U ↦ FrobeniusLinearMap.ext (h U)
      subst g
      rfl

/-- A Frobenius-linear structure-sheaf operator restricts to each open subscheme. -/
def restrict (φ : SchemeFrobeniusMap X p) (U : X.Opens) :
    SchemeFrobeniusMap U.toScheme p where
  onOpen V := φ.onOpen (U.ι ''ᵁ V)
  restrict_comm h s := φ.restrict_comm (Set.image_mono h) s

end FrobeniusSplitting.SchemeFrobeniusMap
