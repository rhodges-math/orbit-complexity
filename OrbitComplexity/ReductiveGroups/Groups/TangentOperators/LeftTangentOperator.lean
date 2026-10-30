import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Left Tangent Operator

Contract the first coordinate of comultiplication with a
counit-valued tangent. Naturality preserves the original coordinate kernel. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

variable {K A B : Type*} [Field K] [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]

/-- The scalar-valued linear functional underlying a tangent. -/
def scalarTangentLinear
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) : A →ₗ[K] K :=
  (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K).toLinearMap.comp d.toLinearMap

/-- First-factor contraction of comultiplication. For matrix coordinates
this gives the row action XU.  -/
def leftTangentOperator
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) : Module.End K A :=
  (TensorProduct.lid K A).toLinearMap.comp
    ((TensorProduct.map (scalarTangentLinear d) LinearMap.id).comp
      (Coalgebra.comul (R := K)))

/-- The coordinate map intertwines the original tangent operators. -/
theorem leftTangentOperator_natural
    (ρ : A →ₐc[K] B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) (a : A) :
    ρ (leftTangentOperator (TauCeti.derivationComp (B := K) ρ d) a) =
      leftTangentOperator d (ρ a) := by
  have ht (z : A ⊗[K] A) :
      ρ ((TensorProduct.lid K A)
        (TensorProduct.map
          (scalarTangentLinear (TauCeti.derivationComp (B := K) ρ d)) LinearMap.id z)) =
      (TensorProduct.lid K B)
        (TensorProduct.map (scalarTangentLinear d) LinearMap.id
          (TensorProduct.map ρ.toLinearMap ρ.toLinearMap z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.lid_tmul, map_smul]
      congr 1
    | add z w hz hw => simp only [map_add, hz, hw]
  change ρ ((TensorProduct.lid K A) (TensorProduct.map _ _ (Coalgebra.comul a))) =
    (TensorProduct.lid K B) (TensorProduct.map _ _ (Coalgebra.comul (ρ a)))
  rw [← CoalgHomClass.map_comp_comul_apply ρ a]
  exact ht _

/-- Invariance of the original defining kernel follows directly from
naturality. -/
theorem leftTangentOperator_preserves_kernel
    (ρ : A →ₐc[K] B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (a : A) (ha : ρ a = 0) :
    ρ (leftTangentOperator (TauCeti.derivationComp (B := K) ρ d) a) = 0 := by
  rw [leftTangentOperator_natural, ha, map_zero]

/-- Counit evaluation recovers the same tangent functional. -/
theorem counit_leftTangentOperator
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) (a : A) :
    Coalgebra.counit (R := K) (leftTangentOperator d a) = scalarTangentLinear d a := by
  have ht (z : A ⊗[K] A) :
      Coalgebra.counit (R := K)
        ((TensorProduct.lid K A) (TensorProduct.map (scalarTangentLinear d) LinearMap.id z)) =
      scalarTangentLinear d ((TensorProduct.rid K A)
        ((Coalgebra.counit (R := K) : A →ₗ[K] K).lTensor A z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [mul_comm]
    | add z w hz hw => simp only [map_add, hz, hw]
  change Coalgebra.counit (R := K)
    ((TensorProduct.lid K A) (TensorProduct.map _ _ (Coalgebra.comul a))) = _
  rw [ht, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

end ReductiveGroups
