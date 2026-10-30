import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalTorusSubgroup
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat

/-!
# The general linear group: smoothness, connectedness, and the diagonal torus

The coordinate Hopf algebra of `GL_n` over a commutative ring `R` is the localization
`R[X_ij][det(X)⁻¹]` of a polynomial ring at one element. Hence it is smooth over `R`, and it is
an integral domain whenever `R` is. Its formation commutes with base change, so over a field it is
geometrically integral and in particular geometrically connected.

The restriction of functions to the diagonal torus is the surjective Hopf-algebra morphism
`O(GL_n) → K[ℤⁿ]` sending `X_ij` to `δ_ij t_i`; its kernel is the Hopf ideal of the diagonal
torus.

## Main declarations

* `ReductiveGroups.GLn.smooth`: `O(GL_n)` is smooth.
* `ReductiveGroups.GLn.geometricallyConnected`: `GL_n` is geometrically connected.
* `ReductiveGroups.GLn.torusRestriction`, `ReductiveGroups.GLn.torusIdeal`: restriction to the
diagonal
  torus and its kernel, with `torusRestriction_eq_zero_iff`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §1.6 and §8.
* J. S. Milne, *Algebraic Groups* (2017), §§1.c, 2.a and Example 12.6.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §2.1.
-/

noncomputable section
namespace ReductiveGroups.GLn

open TauCeti TauCeti.GeneralLinear CategoryTheory
open scoped TensorProduct

universe u

section Ring

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coordinate Hopf algebra of `GL_n` is smooth: it is the localization of a polynomial ring
at the generic determinant. -/
theorem smooth : Algebra.Smooth R (coordinateHopfAlgebra R n) := by
  let _ : Algebra.Smooth R (MatrixMonoid.CoordinateRing R n) := ⟨inferInstance, inferInstance⟩
  let _ : Algebra.Smooth (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n) :=
    Algebra.Smooth.of_isLocalization_Away
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
  let _ : Algebra.Smooth R (CoordinateRing R n) :=
    Algebra.Smooth.comp R (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n)
  exact Algebra.Smooth.of_equiv (coordinateHopfAlgebraAlgEquiv R n)

/-- Over an integral domain, the coordinate Hopf algebra of `GL_n` is an integral domain. -/
theorem isDomain [IsDomain R] : IsDomain (coordinateHopfAlgebra R n) := by
  let _ : IsDomain (CoordinateRing R n) :=
    Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero (Fin n) R)
  exact (coordinateHopfAlgebraAlgEquiv R n).toRingEquiv.isDomain_iff.mp inferInstance

end Ring

/-- `GL_n` is geometrically connected: after every field extension its coordinate ring is again
the coordinate ring of `GL_n`, an integral domain. -/
theorem geometricallyConnected (k : Type u) [Field k] (n : ℕ) :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let _ : IsDomain (coordinateHopfAlgebra L n) := isDomain L n
  let e : coordinateHopfAlgebra k n ⊗[k] L ≃+* coordinateHopfAlgebra L n :=
    (Algebra.TensorProduct.comm k (coordinateHopfAlgebra k n) L).toRingEquiv.trans
      (coordinateHopfAlgebraBaseChangeBialgEquiv k L n).toAlgEquiv.toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr inferInstance

section Torus

variable (K : Type u) [Field K] (n : ℕ)

/-- Restriction of functions on `GL_n` to the diagonal torus, with values in the Laurent
polynomial ring `K[ℤⁿ]` of the split torus. -/
def torusRestriction :
    coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) :=
  (diagonalTorusCoordinateMap (R := K) (N := n)).hom

/-- Restriction to the diagonal torus sends `X_ij` to `δ_ij t_i`. -/
theorem torusRestriction_genericMatrix (i j : Fin n) :
    torusRestriction K n (genericMatrix K n i j) =
      if i = j then
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1
      else 0 := by
  rw [genericMatrix_apply]
  exact diagonalTorusCoordinateMap_X (R := K) (N := n) i j

/-- Restriction to the diagonal torus is surjective. -/
theorem torusRestriction_surjective : Function.Surjective (torusRestriction K n) :=
  diagonalTorusCoordinateMap_surjective

/-- The Hopf ideal of the diagonal torus. -/
def torusIdeal : HopfIdeal K (coordinateHopfAlgebra K n) :=
  diagonalMatrixHopfIdeal (K := K) n

/-- The diagonal-torus ideal is the kernel of restriction to the diagonal torus. -/
theorem torusRestriction_eq_zero_iff (a : coordinateHopfAlgebra K n) :
    torusRestriction K n a = 0 ↔ a ∈ (torusIdeal K n).toIdeal := by
  rw [HopfIdeal.mem_toIdeal]
  exact (HopfIdeal.mem_kerOfSurjective (torusRestriction K n)
    (torusRestriction_surjective K n)).symm

/-- The coordinate Hopf algebra of `GL_n` is of finite type. -/
instance finiteType : Algebra.FiniteType K (coordinateHopfAlgebra K n) := inferInstance

end Torus

end GLn
