import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.SectionCoframeTransport
import OrbitComplexity.FrobeniusSplitting.Splittings.NormalizedFrameUnits
import Batteries.Tactic.Lint

/-! # Polynomial covariance of a common section

The line comparison and the equality of its section first determine the
whole polynomial coordinate change. Prior normalization and its leading
coefficient identify the coframe multiplier.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open Polynomial

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def affineMap {R : Type u} [CommRing R] (a b : R) :
    Polynomial R →+* Polynomial R :=
  (Polynomial.aeval (C a * X + C b)).toRingHom

end FrobeniusSplitting.RetainedCharacter
