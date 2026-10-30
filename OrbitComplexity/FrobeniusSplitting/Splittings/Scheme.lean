import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.AlgebraicGeometry.Properties

/-!
# Frobenius splittings of schemes

A splitting of a scheme is a family of splittings on rings of sections commuting
with restriction. For an exponent greater than one, every such scheme is reduced.

## Main definitions

* `FrobeniusSplitting.SchemeSplitting`: a splitting of the structure sheaf.

## Main results

* `FrobeniusSplitting.SchemeSplitting.isReduced`: a split scheme is reduced.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Definition 1.1.3,
  Remark 1.1.4 and Proposition 1.2.1.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite

/-- Frobenius-linear retractions on the structure sheaf that commute with restriction. -/
structure SchemeSplitting (X : Scheme) (p : ℕ) where
  /-- The splitting on the sections over an open subset. -/
  onOpen (U : X.Opens) : RingSplitting Γ(X, U) p
  /-- Splitting a section commutes with restriction to a smaller open subset. -/
  restrict_comm {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    onOpen V (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (onOpen U s)

namespace SchemeSplitting

variable {X : Scheme} {p : ℕ}

/-- Two scheme splittings agree if they have the same values on sections. -/
@[ext]
theorem ext {splitting other : SchemeSplitting X p}
    (heq : ∀ U s, splitting.onOpen U s = other.onOpen U s) :
    splitting = other := by
  cases splitting
  cases other
  congr
  funext U
  exact RingSplitting.ext (heq U)

/-- A scheme with a Frobenius splitting of exponent greater than one is reduced. -/
theorem isReduced (splitting : SchemeSplitting X p) (hp : 1 < p) :
    AlgebraicGeometry.IsReduced X :=
  ⟨fun U ↦ (splitting.onOpen U).isReduced hp⟩

end SchemeSplitting

end FrobeniusSplitting
