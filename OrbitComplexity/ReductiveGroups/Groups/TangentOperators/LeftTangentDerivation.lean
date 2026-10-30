import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentOperator

/-!
# Left Tangent Derivation

The first-factor tangent contraction satisfies the ordinary derivation
law on the original coordinate algebra. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

variable {K A : Type*} [Field K] [CommRing A] [HopfAlgebra K A]

/-- The equality is

```lean
scalarTangentLinear d (a * b) =
      Coalgebra.counit (R := K) a * scalarTangentLinear d b +
        Coalgebra.counit (R := K) b * scalarTangentLinear d a
```
-/
theorem scalarTangentLinear_mul
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) (a b : A) :
    scalarTangentLinear d (a * b) =
      Coalgebra.counit (R := K) a * scalarTangentLinear d b +
        Coalgebra.counit (R := K) b * scalarTangentLinear d a := by
  change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K) (d (a * b)) = _
  rw [d.leibniz, map_add,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul]
  rfl

/-- The Leibniz identity is obtained before restricting to any coordinate
presentation or finite-dimensional truncation. -/
theorem leftTangentOperator_mul
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) (a b : A) :
    leftTangentOperator d (a * b) =
      a * leftTangentOperator d b + b * leftTangentOperator d a := by
  let D : A ⊗[K] A →ₗ[K] A :=
    (TensorProduct.lid K A).toLinearMap.comp
      (TensorProduct.map (scalarTangentLinear d) LinearMap.id)
  let E : A ⊗[K] A →ₐ[K] A := Algebra.TensorProduct.productMap
    ((Algebra.ofId K A).comp (Bialgebra.counitAlgHom K A)) (AlgHom.id K A)
  have hD (z w : A ⊗[K] A) : D (z * w) = E z * D w + E w * D z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      induction w using TensorProduct.inductionOn with
      | tmul z w =>
        simp [D, E, scalarTangentLinear_mul, Algebra.smul_def]
        ring
      | add z w hz hw => simp only [mul_add, map_add, hz, hw, add_mul]; ring
    | add z w hz hw => simp only [add_mul, map_add, hz, hw, mul_add]; ring
  have hE (x : A) : E (Coalgebra.comul x) = x := by
    have hlin : E.toLinearMap = (TensorProduct.lid K A).toLinearMap.comp
        ((Coalgebra.counit (R := K) : A →ₗ[K] K).rTensor A) := by
      ext x y
      simp [E, Algebra.smul_def]
    change E.toLinearMap (Coalgebra.comul x) = x
    rw [hlin, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
    simp
  change D ((Bialgebra.comulAlgHom K A) (a * b)) =
    a * D (Coalgebra.comul b) + b * D (Coalgebra.comul a)
  rw [map_mul, hD]
  change E (Coalgebra.comul a) * D (Coalgebra.comul b) +
    E (Coalgebra.comul b) * D (Coalgebra.comul a) = _
  rw [hE, hE]

/-- The coordinate-algebra derivation associated to the original tangent
by first-factor contraction. -/
def leftTangentDerivation
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
    Derivation K A A where
  toLinearMap := leftTangentOperator d
  map_one_eq_zero' := by
    have h := leftTangentOperator_mul d 1 1
    simp only [one_mul] at h
    exact add_left_cancel (show leftTangentOperator d 1 + leftTangentOperator d 1 =
      leftTangentOperator d 1 + 0 by simpa using h.symm)
  leibniz' := fun a b => by
    simpa only [smul_eq_mul] using leftTangentOperator_mul d a b

end ReductiveGroups
