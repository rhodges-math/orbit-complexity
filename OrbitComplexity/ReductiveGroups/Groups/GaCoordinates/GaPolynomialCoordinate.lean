import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Ga Polynomial Coordinate

The rank-one symmetric coordinate algebra in ordinary polynomial coordinates. -/

noncomputable section
namespace ReductiveGroups

variable (K : Type*) [CommRing K]

/-- The `K`-algebra isomorphism between the additive group's coordinate algebra `SymmetricAlgebra K
K` and the polynomial ring `K[X]`, sending `SymmetricAlgebra.ι K K 1` to `X`. -/
def gaPolynomialEquiv : SymmetricAlgebra K K ≃ₐ[K] Polynomial K :=
  (TauCeti.AdditiveGroup.coordinateAlgEquiv K).trans
    (MvPolynomial.uniqueAlgEquiv K (TauCeti.AdditiveGroup.CoordinateIndex))

/-- The equality is

```lean
gaPolynomialEquiv K (SymmetricAlgebra.ι K K 1) = Polynomial.X
```
-/
@[simp]
theorem gaPolynomialEquiv_generator :
    gaPolynomialEquiv K (SymmetricAlgebra.ι K K 1) = Polynomial.X := by
  simp [gaPolynomialEquiv]

/-- Evaluating ordinary polynomial coordinates at `t` is the
additive-group point with parameter `t`. -/
theorem gaPolynomialEquiv_eval_point (t : K) (a : SymmetricAlgebra K K) :
    (gaPolynomialEquiv K a).eval t =
      ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd t)).ofConv a := by
  let f : SymmetricAlgebra K K →ₐ[K] K :=
    (Polynomial.aeval t).comp (gaPolynomialEquiv K).toAlgHom
  let g : SymmetricAlgebra K K →ₐ[K] K :=
    ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
      (Multiplicative.ofAdd t)).ofConv
  have hfg : f = g := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    have hι : SymmetricAlgebra.ι K K x =
        x • SymmetricAlgebra.ι K K 1 := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (SymmetricAlgebra.ι K K) x (1 : K))
    have hgen : f (SymmetricAlgebra.ι K K 1) =
        g (SymmetricAlgebra.ι K K 1) := by
      simp [f, g, gaPolynomialEquiv_generator,
        TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι]
    change f (SymmetricAlgebra.ι K K x) = g (SymmetricAlgebra.ι K K x)
    rw [hι, map_smul, map_smul, hgen]
  exact congrArg (fun h : SymmetricAlgebra K K →ₐ[K] K => h a) hfg

end ReductiveGroups
