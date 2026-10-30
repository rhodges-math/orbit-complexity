import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryForms
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup

/-!
# Algebraic representations on homogeneous binary forms

The multiplicative binary-form matrices give comodules and coordinate Hopf
morphisms from the special linear group into general linear groups.
-/

noncomputable section

namespace ReductiveGroups.BinaryForms

open TauCeti Module WithConv
open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]

/-- The defining two-dimensional matrix on the special linear coordinate algebra. -/
def standardMatrix :
    Matrix (Fin 2) (Fin 2) (SpecialLinear.coordinateHopfAlgebra R 2) :=
  (GeneralLinear.genericMatrix R 2).map (SpecialLinear.coordinateMap R 2).hom

private theorem standardMatrix_comul :
    (standardMatrix R).map
        (Bialgebra.comulAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) =
      (standardMatrix R).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (standardMatrix R).map (Algebra.TensorProduct.includeRight (R := R)) :=
  Comodule.map_comul_map R (GeneralLinear.genericMatrix R 2)
    (SpecialLinear.coordinateMap R 2).hom (GeneralLinear.map_comul_genericMatrix R 2)

private theorem standardMatrix_counit :
    (standardMatrix R).map
        (Bialgebra.counitAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) = 1 :=
  Comodule.map_counit_map R (GeneralLinear.genericMatrix R 2)
    (SpecialLinear.coordinateMap R 2).hom (GeneralLinear.map_counit_genericMatrix R 2)

private def coefficientMatrix (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (SpecialLinear.coordinateHopfAlgebra R 2) :=
  matrix (SpecialLinear.coordinateHopfAlgebra R 2) n (standardMatrix R)

private theorem coefficientMatrix_comul (n : ℕ) :
    (coefficientMatrix R n).map
        (Bialgebra.comulAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) =
      (coefficientMatrix R n).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (coefficientMatrix R n).map (Algebra.TensorProduct.includeRight (R := R)) := by
  let H := SpecialLinear.coordinateHopfAlgebra R 2
  let f := (Bialgebra.comulAlgHom R H).toRingHom
  let l := (Algebra.TensorProduct.includeLeft (R := R) (S := R) :
    H →ₐ[R] H ⊗[R] H).toRingHom
  let r := (Algebra.TensorProduct.includeRight (R := R) :
    H →ₐ[R] H ⊗[R] H).toRingHom
  calc
    _ = matrix (H ⊗[R] H) n ((standardMatrix R).map f) :=
      (matrix_map H n f (standardMatrix R)).symm
    _ = matrix (H ⊗[R] H) n
        ((standardMatrix R).map l * (standardMatrix R).map r) :=
      congrArg (matrix (H ⊗[R] H) n) (standardMatrix_comul R)
    _ = matrix (H ⊗[R] H) n ((standardMatrix R).map l) *
        matrix (H ⊗[R] H) n ((standardMatrix R).map r) := matrix_mul _ n _ _
    _ = _ := congrArg₂ (· * ·) (matrix_map H n l (standardMatrix R))
      (matrix_map H n r (standardMatrix R))

private theorem coefficientMatrix_counit (n : ℕ) :
    (coefficientMatrix R n).map
        (Bialgebra.counitAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) = 1 := by
  let H := SpecialLinear.coordinateHopfAlgebra R 2
  calc
    _ = matrix R n ((standardMatrix R).map (Bialgebra.counitAlgHom R H).toRingHom) :=
      (matrix_map H n (Bialgebra.counitAlgHom R H).toRingHom (standardMatrix R)).symm
    _ = matrix R n 1 := congrArg (matrix R n) (standardMatrix_counit R)
    _ = _ := matrix_one R n

/-- The special-linear comodule on the coordinates of degree-`n` binary forms. -/
@[instance_reducible]
def comodule (n : ℕ) :
    Comodule R (SpecialLinear.coordinateHopfAlgebra R 2) (Fin (n + 1) → R) :=
  Comodule.matrixComodule R (coefficientMatrix R n) (coefficientMatrix_comul R n)
    (Comodule.counit_basisFun_of_map_counit R _ (coefficientMatrix_counit R n))

/-- The coordinate Hopf morphism of the degree-`n` binary-form representation. -/
def coordinateMap (n : ℕ) :
    GeneralLinear.coordinateHopfAlgebra R (n + 1) →ₐc[R]
      SpecialLinear.coordinateHopfAlgebra R 2 :=
  letI := comodule R n
  Comodule.coordinateBialgHom (Pi.basisFun R (Fin (n + 1)))

/-- The binary-form coordinate morphism has its specified coefficient matrix. -/
theorem coordinateMap_matrix (n : ℕ) :
    (GeneralLinear.genericMatrix R (n + 1)).map (coordinateMap R n) =
      matrix (SpecialLinear.coordinateHopfAlgebra R 2) n (standardMatrix R) := by
  let := comodule R n
  ext i j
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply]
  change Comodule.coordinateBialgHom (Pi.basisFun R (Fin (n + 1))) _ = _
  rw [Comodule.coordinateBialgHom_X]
  exact congrFun (congrFun
    (Comodule.coefficientMatrix_matrixComodule R (coefficientMatrix R n)
      (coefficientMatrix_comul R n)
      (Comodule.counit_basisFun_of_map_counit R _ (coefficientMatrix_counit R n))) i) j

variable {A : Type v} [CommRing A] [Algebra R A]

/-- At an algebra-valued point, the representation is the binary-form matrix
of the corresponding two-dimensional matrix. -/
theorem coordinateMap_points (n : ℕ)
    (q : WithConv (SpecialLinear.coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (GeneralLinear.genericMatrix R (n + 1)).map
        (q.ofConv.comp (coordinateMap R n).toAlgHom) =
      matrix A n ((GeneralLinear.genericMatrix R 2).map
        (q.ofConv.comp (SpecialLinear.coordinateMap R 2).hom.toAlgHom)) := by
  let H := SpecialLinear.coordinateHopfAlgebra R 2
  calc
    _ = (matrix H n (standardMatrix R)).map q.ofConv := by
      rw [show (q.ofConv.comp (coordinateMap R n).toAlgHom :
          GeneralLinear.coordinateHopfAlgebra R (n + 1) → A) =
            q.ofConv ∘ coordinateMap R n from rfl]
      rw [← Matrix.map_map, coordinateMap_matrix]
    _ = matrix A n ((standardMatrix R).map q.ofConv) :=
      (matrix_map H n q.ofConv.toRingHom (standardMatrix R)).symm
    _ = _ := rfl

end ReductiveGroups.BinaryForms
