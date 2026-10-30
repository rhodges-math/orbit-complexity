import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateAction
import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateTruncation

/-!
# GL Coordinate Generators

The generic entries and determinant inverse generate the GL
coordinate algebra. The proof uses localization exhaustion and does not
require injectivity of the polynomial presentation. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] (n : ℕ)

/-- The equality is

```lean
S = ⊤
```
-/
theorem glCoordinate_subalgebra_eq_top
    (S : Subalgebra K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))
    (hX : ∀ i j, TauCeti.GeneralLinear.genericMatrix K n i j ∈ S)
    (hu : detInverseCoordinate (K := K) n ∈ S) : S = ⊤ := by
  let π := (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toAlgHom.comp
    (TauCeti.GeneralLinear.coordinateRingMap K n)
  have hp (p : MvPolynomial (Fin n × Fin n) K) : π p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      change π (algebraMap K _ c) ∈ S
      rw [AlgHom.commutes]
      exact S.algebraMap_mem c
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | mul_X p ij hp =>
      rw [map_mul]
      exact S.mul_mem hp (hX ij.1 ij.2)
  apply top_unique
  intro a _
  obtain ⟨r, d, ha⟩ := glCoordinateTruncation_exhaustive n a
  obtain ⟨p, hpresentation⟩ := ha
  change TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
    (TauCeti.GeneralLinear.coordinateRingMap K n (p : MvPolynomial (Fin n × Fin n) K) *
      (IsLocalization.Away.invSelf
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) ^ r) = a at hpresentation
  rw [← hpresentation, map_mul, map_pow]
  exact S.mul_mem (hp p) (S.pow_mem hu r)

/-- An explicit algebra-generating set for the same original coordinate algebra. -/
theorem glCoordinate_adjoin_entries_detInverse :
    Algebra.adjoin K
      (Set.range (fun ij : Fin n × Fin n =>
        TauCeti.GeneralLinear.genericMatrix K n ij.1 ij.2) ∪
        {detInverseCoordinate (K := K) n}) = ⊤ := by
  apply glCoordinate_subalgebra_eq_top n
  · intro i j
    exact Algebra.subset_adjoin (Or.inl ⟨(i, j), rfl⟩)
  · exact Algebra.subset_adjoin (Or.inr rfl)

end ReductiveGroups
