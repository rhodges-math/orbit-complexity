import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Solvable.ConnectedGeneratedSubgroup
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Torus Ga Generator Family

A mixed family consisting of one split torus and any family
of additive-group morphisms into the same original affine group. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K B ι σ : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The codomains of a mixed family of Hopf algebra morphisms indexed by `Option σ`: the group
algebra of `ι →₀ ℤ` (a split torus) at `none` and the additive group's coordinate algebra
`SymmetricAlgebra K K` at each `some i`. -/
def torusGaGeneratorCodomain (K : Type u) [Field K] (ι σ : Type u) :
    Option σ → CommHopfAlgCat.{u} K
  | none => CommHopfAlgCat.of K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
  | some _ => CommHopfAlgCat.of K (SymmetricAlgebra K K)

/-- The mixed family of Hopf algebra morphisms out of `B`: the torus coordinate map `π` at `none`
and the additive-group morphism `x i` at `some i`. -/
def torusGaGeneratorFamily
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (x : σ → B →ₐc[K] SymmetricAlgebra K K) :
    ∀ j, CommHopfAlgCat.of K B ⟶ torusGaGeneratorCodomain K ι σ j
  | none => CommHopfAlgCat.ofHom π
  | some i => CommHopfAlgCat.ofHom (x i)

/-- For these parameters,

```lean
Algebra.FiniteType K (torusGaGeneratorCodomain K ι σ j)
```
-/
theorem torusGaGeneratorCodomain_finiteType [Algebra.FiniteType K B]
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (j : Option σ) :
    Algebra.FiniteType K (torusGaGeneratorCodomain K ι σ j) := by
  cases j with
  | none => exact Algebra.FiniteType.of_surjective π.toAlgHom hπ
  | some i =>
      change Algebra.FiniteType K (SymmetricAlgebra K K)
      exact Algebra.FiniteType.of_surjective (gaPolynomialEquiv K).symm.toAlgHom
        (gaPolynomialEquiv K).symm.surjective

/-- For these parameters,

```lean
IsDomain (torusGaGeneratorCodomain K ι σ j)
```
-/
theorem torusGaGeneratorCodomain_isDomain (j : Option σ) :
    IsDomain (torusGaGeneratorCodomain K ι σ j) := by
  cases j with
  | none =>
      change IsDomain (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      infer_instance
  | some i =>
      change IsDomain (SymmetricAlgebra K K)
      exact (gaPolynomialEquiv K).injective.isDomain

end ReductiveGroups
