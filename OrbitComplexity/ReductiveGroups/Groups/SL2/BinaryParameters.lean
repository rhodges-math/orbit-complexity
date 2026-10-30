import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryComodule
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPolynomialCoordinate

/-! # Elementary subgroup coordinates of binary forms -/

noncomputable section

namespace ReductiveGroups.BinaryForms

open TauCeti WithConv
open scoped Matrix

universe u
variable (R : Type u) [CommRing R]

/-- Restriction of the binary-form representation to an elementary subgroup. -/
def rootCoordinateMap (n : ℕ) {i j : Fin 2} (hij : i ≠ j) :
    GeneralLinear.coordinateHopfAlgebra R (n + 1) →ₐc[R] SymmetricAlgebra R R :=
  (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom.comp (coordinateMap R n)

private theorem elementary_matrix {i j : Fin 2} (hij : i ≠ j) :
    (GeneralLinear.genericMatrix R 2).map
        ((SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom.toAlgHom.comp
          (SpecialLinear.coordinateMap R 2).hom.toAlgHom) =
      1 + Matrix.single i j (SymmetricAlgebra.ι R R 1) := by
  have h := congrArg (fun f => f.hom)
    (SpecialLinear.coordinateMap_comp_rootSubgroupCoordinateMap (R := R) hij)
  have heq : (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom.comp
      (SpecialLinear.coordinateMap R 2).hom =
        (GeneralLinear.rootSubgroupCoordinateMap (R := R) hij).hom := h
  ext a b
  change ((SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom.comp
    (SpecialLinear.coordinateMap R 2).hom) _ = _
  rw [heq, GeneralLinear.genericMatrix_apply]
  exact GeneralLinear.rootSubgroupCoordinateMap_apply_X hij a b

/-- The elementary subgroup has the elementary binary-form coefficient matrix. -/
theorem rootCoordinateMap_matrix (n : ℕ) {i j : Fin 2} (hij : i ≠ j) :
    (GeneralLinear.genericMatrix R (n + 1)).map (rootCoordinateMap R n hij) =
      matrix (SymmetricAlgebra R R) n
        (1 + Matrix.single i j (SymmetricAlgebra.ι R R 1)) := by
  have h := coordinateMap_points R n
    (toConv (SpecialLinear.rootSubgroupCoordinateMap (R := R) hij).hom.toAlgHom)
  change _ = matrix _ n _ at h
  rw [elementary_matrix R hij] at h
  exact h

/-- Ordinary polynomial coordinates express the elementary parameter as `X`. -/
theorem rootCoordinateMap_polynomial (n : ℕ) {i j : Fin 2} (hij : i ≠ j) :
    (GeneralLinear.genericMatrix R (n + 1)).map
        (fun p => gaPolynomialEquiv R (rootCoordinateMap R n hij p)) =
      matrix (Polynomial R) n (1 + Matrix.single i j Polynomial.X) := by
  let f := (gaPolynomialEquiv R).toRingHom
  calc
    _ = ((GeneralLinear.genericMatrix R (n + 1)).map
        (rootCoordinateMap R n hij)).map f := rfl
    _ = (matrix (SymmetricAlgebra R R) n
        (1 + Matrix.single i j (SymmetricAlgebra.ι R R 1))).map f :=
      congrArg (fun a => a.map f) (rootCoordinateMap_matrix R n hij)
    _ = matrix (Polynomial R) n
        ((1 + Matrix.single i j (SymmetricAlgebra.ι R R 1)).map f) :=
      (matrix_map (SymmetricAlgebra R R) n f _).symm
    _ = _ := by
      congr 1
      apply Matrix.ext
      intro a b
      by_cases h : i = a ∧ j = b <;>
        simp [f, Matrix.single, Matrix.one_apply, h]

end ReductiveGroups.BinaryForms
