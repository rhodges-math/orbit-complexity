import OrbitComplexity.FrobeniusSplitting.Compatible.Ideals

/-! # Frobenius-linear operators and weighted splittings -/

namespace FrobeniusSplitting

/-- An additive operator linear with respect to Frobenius multiplication. -/
structure FrobeniusLinearMap (R : Type*) [CommSemiring R] (p : ℕ) where
  /-- The underlying additive operator. -/
  toAddMonoidHom : R →+ R
  /-- Frobenius linearity with respect to multiplication. -/
  map_pow_mul' (a b : R) : toAddMonoidHom (a ^ p * b) = a * toAddMonoidHom b

namespace FrobeniusLinearMap

variable {R : Type*} [CommSemiring R] {p : ℕ}

/-- Frobenius-linear operators act on ring elements through their additive map. -/
instance : CoeFun (FrobeniusLinearMap R p) (fun _ ↦ R → R) :=
  ⟨fun φ ↦ φ.toAddMonoidHom⟩

/-- A Frobenius-linear operator takes zero to zero. -/
@[simp]
theorem map_zero (φ : FrobeniusLinearMap R p) : φ 0 = 0 := φ.toAddMonoidHom.map_zero

/-- A Frobenius-linear operator preserves addition. -/
theorem map_add (φ : FrobeniusLinearMap R p) (a b : R) : φ (a + b) = φ a + φ b :=
  φ.toAddMonoidHom.map_add a b

/-- Frobenius linearity can be applied through the operator notation. -/
theorem map_pow_mul (φ : FrobeniusLinearMap R p) (a b : R) :
    φ (a ^ p * b) = a * φ b := φ.map_pow_mul' a b

/-- Weighting a Frobenius-linear operator by an element mapping to one gives a splitting. -/
def toSplitting (φ : FrobeniusLinearMap R p) (c : R) (hc : φ c = 1) : RingSplitting R p where
  toAddMonoidHom :=
    { toFun := fun a ↦ φ (c * a)
      map_zero' := by rw [mul_zero, φ.map_zero]
      map_add' a b := by rw [mul_add, φ.map_add] }
  map_pow_mul' a b := by
    change φ (c * (a ^ p * b)) = a * φ (c * b)
    rw [← mul_assoc, mul_comm c (a ^ p), mul_assoc, φ.map_pow_mul]
  map_one' := by
    change φ (c * 1) = 1
    rw [mul_one, hc]

/-- The weighted splitting applies its operator after multiplying by the weight. -/
theorem toSplitting_apply (φ : FrobeniusLinearMap R p) (c : R) (hc : φ c = 1) (a : R) :
    φ.toSplitting c hc a = φ (c * a) := rfl

end FrobeniusLinearMap

/-- Weighting by a divisor to the characteristic minus one preserves its principal ideal. -/
theorem FrobeniusLinearMap.toSplitting_compatible_span {R : Type*} [CommRing R] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) (f : R) (hf : φ (f ^ (p - 1)) = 1) :
    (φ.toSplitting (f ^ (p - 1)) hf).IsCompatible (Ideal.span {f}) := by
  intro a ha
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  refine ⟨φ b, ?_⟩
  change φ (f ^ (p - 1) * (f * b)) = f * φ b
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp, φ.map_pow_mul]


end FrobeniusSplitting
