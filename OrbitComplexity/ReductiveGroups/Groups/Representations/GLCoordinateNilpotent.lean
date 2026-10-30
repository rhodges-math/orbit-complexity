import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateGenerators
import OrbitComplexity.ReductiveGroups.Lie.Exponential.MatrixRowNilpotence

/-!
# GL Coordinate Nilpotent

A nilpotent tangent matrix induces a locally nilpotent derivation on the
localized GL coordinate algebra. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] (n : ℕ)
variable (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
  (TauCeti.Bialgebra.CounitAlgebra K
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))

/-- The equality is

```lean
scalarTangentLinear d (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)) =
      Matrix.trace (TauCeti.GeneralLinear.tangentMatrix n d)
```
-/
theorem scalarTangentLinear_det_genericMatrix :
    scalarTangentLinear d (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)) =
      Matrix.trace (TauCeti.GeneralLinear.tangentMatrix n d) := by
  have hdet : Matrix.det (TauCeti.GeneralLinear.genericMatrix K n) =
      (TauCeti.GeneralLinear.determinantGroupLike K n :
        TauCeti.GeneralLinear.coordinateHopfAlgebra K n) := by
    rw [TauCeti.GeneralLinear.determinantGroupLike_val]
    change ((TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toAlgHom.mapMatrix
      (TauCeti.GeneralLinear.localizedGenericMatrix K n)).det = _
    exact (AlgHom.map_det (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toAlgHom
      (TauCeti.GeneralLinear.localizedGenericMatrix K n)).symm
  rw [hdet, TauCeti.GeneralLinear.trace_tangentMatrix]
  rfl

/-- The invariant derivation of a nilpotent matrix is locally nilpotent
on every coordinate, including all determinant denominators. -/
theorem GlCoordinate.leftTangent_locally_nilpotent
    (hd : IsNilpotent (TauCeti.GeneralLinear.tangentMatrix n d)) :
    ∀ a : TauCeti.GeneralLinear.coordinateHopfAlgebra K n,
      ∃ m : ℕ, (leftTangentOperator d ^ m) a = 0 := by
  have hS : derivationNilpotentSubalgebra (leftTangentDerivation d) = ⊤ := by
    apply glCoordinate_subalgebra_eq_top n
    · intro i j
      change ∃ m : ℕ, (leftTangentOperator d ^ m)
        (TauCeti.GeneralLinear.genericMatrix K n i j) = 0
      exact end_row_locally_nilpotent (leftTangentOperator d)
        (TauCeti.GeneralLinear.tangentMatrix n d)
        (fun i => TauCeti.GeneralLinear.genericMatrix K n i j)
        (fun i => leftTangentOperator_genericMatrix_apply n d i j) hd i
    · change ∃ m : ℕ, (leftTangentOperator d ^ m) (detInverseCoordinate (K := K) n) = 0
      refine ⟨1, ?_⟩
      rw [pow_one, leftTangentOperator_detInverseCoordinate,
        scalarTangentLinear_det_genericMatrix]
      have ht : Matrix.trace (TauCeti.GeneralLinear.tangentMatrix n d) = 0 :=
        (Matrix.isNilpotent_trace_of_isNilpotent hd).eq_zero
      rw [ht, neg_zero, zero_smul]
  intro a
  have ha : a ∈ derivationNilpotentSubalgebra (leftTangentDerivation d) := by
    rw [hS]
    trivial
  exact ha

/-- In particular every finite invariant subspace of GL coordinates
has nilpotent restricted operator. -/
theorem GlCoordinate.leftTangent_restrict_isNilpotent
    (hd : IsNilpotent (TauCeti.GeneralLinear.tangentMatrix n d))
    (W : Submodule K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))
    [FiniteDimensional K W] (hW : W ∈ (leftTangentOperator d).invtSubmodule) :
    IsNilpotent ((leftTangentOperator d).restrict hW) :=
  DerivationLocalNilpotence.isNilpotent_of_locally_nilpotent (leftTangentOperator d) W hW
    (fun a _ => GlCoordinate.leftTangent_locally_nilpotent n d hd a)

end ReductiveGroups
