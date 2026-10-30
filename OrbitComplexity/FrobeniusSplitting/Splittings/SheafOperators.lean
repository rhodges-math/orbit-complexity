import OrbitComplexity.FrobeniusSplitting.Splittings.LinearMap
import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme
import OrbitComplexity.FrobeniusSplitting.Normality.DenseOpen

/-!
# Frobenius-linear structure-sheaf operators

Frobenius-linear operators on all rings of sections that commute with restriction can be
normalized by a global weight. On a reduced Noetherian scheme it suffices to check that the
weight maps to one on a dense open subset.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

/-- Frobenius-linear operators on the structure sheaf commuting with restriction. -/
structure SchemeFrobeniusMap (X : Scheme) (p : ℕ) where
  /-- The operator on sections over an open subset. -/
  onOpen (U : X.Opens) : FrobeniusLinearMap Γ(X, U) p
  /-- The operators commute with restriction of sections. -/
  restrict_comm {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    onOpen V (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (onOpen U s)

namespace SchemeFrobeniusMap

variable {X : Scheme} {p : ℕ}

/-- A global section taken to one normalizes a structure-sheaf operator to a splitting. -/
def toSplitting (φ : SchemeFrobeniusMap X p) (c : Γ(X, ⊤))
    (hc : φ.onOpen ⊤ c = 1) : SchemeSplitting X p where
  onOpen U := (φ.onOpen U).toSplitting (X.presheaf.map (homOfLE le_top).op c) (by
    rw [φ.restrict_comm, hc, map_one])
  restrict_comm {U V} h s := by
    have ht : X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c) =
        X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op c := by
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl
    change φ.onOpen V (X.presheaf.map (homOfLE le_top).op c *
      X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (φ.onOpen U
        (X.presheaf.map (homOfLE le_top).op c * s))
    rw [← φ.restrict_comm h]
    congr 1
    rw [map_mul, ht]

/-- The normalized sheaf operator multiplies by the restricted global weight. -/
theorem toSplitting_apply (φ : SchemeFrobeniusMap X p) (c : Γ(X, ⊤))
    (hc : φ.onOpen ⊤ c = 1) (U : X.Opens) (s : Γ(X, U)) :
    (φ.toSplitting c hc).onOpen U s =
      φ.onOpen U (X.presheaf.map (homOfLE le_top).op c * s) := rfl

/-- Normalization may be checked on one dense open of a reduced Noetherian scheme. -/
def toSplittingOfDense [IsReduced X] [NoetherianSpace X]
    (φ : SchemeFrobeniusMap X p) (c : Γ(X, ⊤)) (U : X.Opens)
    (hd : Dense (U : Set X))
    (hc : φ.onOpen U (X.presheaf.map (homOfLE le_top).op c) = 1) :
    SchemeSplitting X p :=
  φ.toSplitting c (by
    apply restrict_injective U hd
    rw [← φ.restrict_comm le_top, hc, map_one])

end SchemeFrobeniusMap

end FrobeniusSplitting
