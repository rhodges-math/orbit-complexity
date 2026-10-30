import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentOperator

/-!
# Left Tangent Linearity

Additivity of the first-factor coordinate operator. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

variable {K A : Type*} [Field K] [CommRing A] [HopfAlgebra K A]

/-- The equality is

```lean
leftTangentOperator (d + e) = leftTangentOperator d + leftTangentOperator e
```
-/
theorem leftTangentOperator_add
    (d e : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
    leftTangentOperator (d + e) = leftTangentOperator d + leftTangentOperator e := by
  have hadd (a : A) : scalarTangentLinear (d + e) a =
      scalarTangentLinear d a + scalarTangentLinear e a := by
    change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K) (d a + e a) = _
    exact map_add _ _ _
  have ht (z : A ⊗[K] A) :
      (TensorProduct.lid K A) (TensorProduct.map (scalarTangentLinear (d + e)) LinearMap.id z) =
      (TensorProduct.lid K A) (TensorProduct.map (scalarTangentLinear d) LinearMap.id z) +
        (TensorProduct.lid K A) (TensorProduct.map (scalarTangentLinear e) LinearMap.id z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
        hadd, add_smul]
    | add z w hz hw =>
      simp only [map_add, hz, hw]
      abel
  ext a
  exact ht (Coalgebra.comul a)

/-- The equality is

```lean
leftTangentOperator (r • d) = r • leftTangentOperator d
```
-/
theorem leftTangentOperator_smul
    (r : K) (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
    leftTangentOperator (r • d) = r • leftTangentOperator d := by
  have hsmul (a : A) : scalarTangentLinear (r • d) a = r • scalarTangentLinear d a := by
    change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K) (r • d a) = _
    exact map_smul _ _ _
  have ht (z : A ⊗[K] A) :
      (TensorProduct.lid K A) (TensorProduct.map (scalarTangentLinear (r • d)) LinearMap.id z) =
      r • (TensorProduct.lid K A) (TensorProduct.map (scalarTangentLinear d) LinearMap.id z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
        hsmul, smul_eq_mul, smul_smul]
    | add z w hz hw => simp only [map_add, hz, hw, smul_add]
  ext a
  exact ht (Coalgebra.comul a)

/-- Counit recovery makes the coordinate-operator construction faithful. -/
theorem leftTangentOperator_injective :
    Function.Injective (leftTangentOperator (K := K) (A := A)) := by
  intro d e h
  ext a
  apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K).injective
  change scalarTangentLinear d a = scalarTangentLinear e a
  rw [← counit_leftTangentOperator, ← counit_leftTangentOperator, h]

end ReductiveGroups
