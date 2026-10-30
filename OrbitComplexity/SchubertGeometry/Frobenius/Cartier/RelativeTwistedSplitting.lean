import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedCoefficients
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSection
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The compatible splitting induced by the relative Cartier map -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open private splittingFrame splittingOperator_eq
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedCoefficients

open private line sourceLine relativeBase
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A] [ExpChar A p]

private def normalizedRelativeOperator (base : RingSplitting A p) :
    SchemeFrobeniusMap (line A) p :=
  twistedSectionOperator (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (relativeTwistedCartierMap (K := K) base.toOperator)
    (((splittingFrame A p).val.app (op ⊤)).hom (1 : Γ(line A, ⊤)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: splittingOperator_value"

private theorem splittingOperator_value {X : Scheme.{u}} {q : ℕ}
    (σ : SchemeSplitting X q) (U : X.Opens) (a : Γ(X, U)) :
    σ.toOperator.onOpen U a = σ.onOpen U a := rfl

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: normalizedRelativeOperator_eq"

private theorem normalizedRelativeOperator_eq (base : RingSplitting A p) :
    normalizedRelativeOperator (K := K) base = (projectiveLineSplitting base).toOperator :=
  (twistedSectionOperator_relative (K := K) base.toOperator (splittingFrame A p)).trans
    (splittingOperator_eq (K := K) base)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: normalizedRelativeOperator_one"

private theorem normalizedRelativeOperator_one (base : RingSplitting A p) :
    (normalizedRelativeOperator (K := K) base).onOpen ⊤ 1 = 1 := by
  have h := congrArg (fun φ : SchemeFrobeniusMap (line A) p => φ.onOpen ⊤ 1)
    (normalizedRelativeOperator_eq (K := K) base)
  exact h.trans (RingSplitting.map_one ((projectiveLineSplitting base).onOpen ⊤))

/-- The relative Cartier map, evaluated on the endpoint section with affine polynomial
`X^(p-1)`, induces a normalized splitting of the projective line. -/
def relativeTwistedSplitting (base : RingSplitting A p) : SchemeSplitting (line A) p :=
  (normalizedRelativeOperator (K := K) base).toSplitting 1
    (normalizedRelativeOperator_one (K := K) base)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: relativeTwistedSplitting_eq"

/-- The splitting induced by the relative Cartier section equals the canonical
projective line splitting of the given base splitting. -/
theorem relativeTwistedSplitting_eq (base : RingSplitting A p) :
    relativeTwistedSplitting (K := K) base = projectiveLineSplitting base := by
  apply SchemeSplitting.ext
  intro U a
  have h := congrArg (fun φ : SchemeFrobeniusMap (line A) p => φ.onOpen U a)
    (normalizedRelativeOperator_eq (K := K) base)
  simpa only [relativeTwistedSplitting, SchemeFrobeniusMap.toSplitting_apply,
    map_one, one_mul, splittingOperator_value] using h

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: relativeTwistedSplitting_sections"

/-- Both zero-coordinate sections have kernels preserved by the splitting induced
from the relative Cartier map. -/
theorem relativeTwistedSplitting_sections (base : RingSplitting A p)
    (j : ULift.{u} (Fin 2)) :
    (relativeTwistedSplitting (K := K) base).IsCompatible (projectiveLineSection A j).ker := by
  rw [relativeTwistedSplitting_eq]
  exact projectiveLineSplitting_sections base j


end SchubertGeometry.ProjectiveCartier
