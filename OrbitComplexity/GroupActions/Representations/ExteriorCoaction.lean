import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Basic
import Mathlib.RingTheory.Bialgebra.Basic

/-! # Coactions on exterior algebras

A coaction on a module extends multiplicatively to its exterior algebra. Base change
constructs the extension, and the coaction laws follow from their values on generators.
-/

noncomputable section
namespace GroupActions
open TauCeti
open scoped TensorProduct

universe u v w
variable {K : Type u} {H : Type v} {V : Type w}
  [Field K] [CharZero K] [CommRing H] [Bialgebra K H]
  [AddCommGroup V] [Module K V] [Comodule K H V]

@[instance_reducible] private noncomputable def invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (by norm_num)
attribute [local instance] invertibleTwo

omit [Comodule K H V] in
private theorem baseChange_zero :
    (0 : QuadraticForm K V).baseChange H = 0 := by
  apply baseChange_ext
  intro v
  simp

/-- The multiplicative coaction extending the given coaction on the generating module. -/
def exteriorCoact :
    ExteriorAlgebra K V →ₐ[K] (ExteriorAlgebra K V) ⊗[K] H := by
  let Q : QuadraticForm H (H ⊗[K] V) := (0 : QuadraticForm K V).baseChange H
  let c : V →ₗ[K] CliffordAlgebra Q :=
    (CliffordAlgebra.ι Q).restrictScalars K ∘ₗ
      (TensorProduct.comm K V H).toLinearMap ∘ₗ Comodule.coact (R := K) (C := H)
  let l : ExteriorAlgebra K V →ₐ[K] CliffordAlgebra Q :=
    ExteriorAlgebra.lift K ⟨c, fun v => by
      change CliffordAlgebra.ι Q _ * CliffordAlgebra.ι Q _ = 0
      rw [CliffordAlgebra.ι_sq_scalar]
      have hQ : Q = 0 := baseChange_zero
      rw [hQ]
      simp⟩
  exact (Algebra.TensorProduct.comm K H (ExteriorAlgebra K V)).toAlgHom.comp
    (((CliffordAlgebra.toBaseChange H (0 : QuadraticForm K V)).restrictScalars K).comp l)

/-- The exterior-algebra coaction agrees with the original coaction on each generator. -/
theorem exteriorCoact_ι (v : V) :
    exteriorCoact (K := K) (H := H) (ExteriorAlgebra.ι K v) =
      TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id
        (Comodule.coact (R := K) (C := H) v) := by
  have ht (z : H ⊗[K] V) :
      Algebra.TensorProduct.comm K H (ExteriorAlgebra K V)
          (CliffordAlgebra.toBaseChange H (0 : QuadraticForm K V)
            (CliffordAlgebra.ι ((0 : QuadraticForm K V).baseChange H) z)) =
        TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id
          (TensorProduct.comm K H V z) := by
    induction z using TensorProduct.inductionOn with
    | tmul h v => simp
    | add z w hz hw => simp only [map_add, hz, hw]
  change Algebra.TensorProduct.comm K H (ExteriorAlgebra K V)
      (CliffordAlgebra.toBaseChange H (0 : QuadraticForm K V)
        ((ExteriorAlgebra.lift K _)
          (ExteriorAlgebra.ι K v))) = _
  rw [ExteriorAlgebra.lift_ι_apply]
  change Algebra.TensorProduct.comm K H (ExteriorAlgebra K V)
      (CliffordAlgebra.toBaseChange H (0 : QuadraticForm K V)
        (CliffordAlgebra.ι ((0 : QuadraticForm K V).baseChange H)
          (TensorProduct.comm K V H (Comodule.coact (R := K) (C := H) v)))) = _
  rw [ht]
  simp only [TensorProduct.comm_comm]


private theorem tensor_coact_ι (z : V ⊗[K] H) :
    TensorProduct.map (exteriorCoact (K := K) (H := H) (V := V)).toLinearMap
        LinearMap.id (TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id z) =
      TensorProduct.map (TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id) LinearMap.id
        ((Comodule.coact (R := K) (C := H) (M := V)).rTensor H z) := by
  induction z using TensorProduct.inductionOn with
  | tmul v h => simp [exteriorCoact_ι]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem exteriorCoact_coassoc :
    (Algebra.TensorProduct.assoc K K K (ExteriorAlgebra K V) H H).toAlgHom.comp
        ((Algebra.TensorProduct.map (exteriorCoact (K := K) (H := H) (V := V))
          (AlgHom.id K H)).comp exteriorCoact) =
      (Algebra.TensorProduct.map (AlgHom.id K (ExteriorAlgebra K V))
        (Bialgebra.comulAlgHom K H)).comp exteriorCoact := by
  ext v
  change TensorProduct.assoc K (ExteriorAlgebra K V) H H
      (TensorProduct.map (exteriorCoact (K := K) (H := H) (V := V)).toLinearMap
        LinearMap.id (exteriorCoact (ExteriorAlgebra.ι K v))) =
    TensorProduct.map LinearMap.id Coalgebra.comul
      (exteriorCoact (ExteriorAlgebra.ι K v))
  rw [exteriorCoact_ι, tensor_coact_ι, ← TensorProduct.map_map_assoc]
  rw [Comodule.coassoc_apply]
  simp only [LinearMap.lTensor_def, TensorProduct.map_map, LinearMap.comp_id,
    LinearMap.id_comp, TensorProduct.map_id]

private theorem exteriorCoact_counit :
    (Algebra.TensorProduct.map (AlgHom.id K (ExteriorAlgebra K V))
        (Bialgebra.counitAlgHom K H)).comp
      (exteriorCoact (K := K) (H := H) (V := V)) =
        (Algebra.TensorProduct.rid K K (ExteriorAlgebra K V)).symm.toAlgHom := by
  ext v
  change Coalgebra.counit.lTensor (ExteriorAlgebra K V)
    (exteriorCoact (ExteriorAlgebra.ι K v)) = ExteriorAlgebra.ι K v ⊗ₜ[K] 1
  rw [exteriorCoact_ι]
  have ht (z : V ⊗[K] H) :
      Coalgebra.counit.lTensor (ExteriorAlgebra K V)
          (TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id z) =
        TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id
          (Coalgebra.counit.lTensor V z) := by
    induction z using TensorProduct.inductionOn with
    | tmul v h => simp
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [ht, Comodule.lTensor_counit_coact]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]

/-- The exterior algebra inherits the multiplicative coaction extending its generators. -/
@[instance_reducible]
def exteriorAlgebraComodule : Comodule K H (ExteriorAlgebra K V) where
  coact := (exteriorCoact (K := K) (H := H) (V := V)).toLinearMap
  coassoc := congrArg AlgHom.toLinearMap exteriorCoact_coassoc
  lTensor_counit_comp_coact := congrArg AlgHom.toLinearMap exteriorCoact_counit

end GroupActions
