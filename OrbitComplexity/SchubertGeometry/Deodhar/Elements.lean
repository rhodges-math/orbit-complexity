import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-! # Deodhar root elements and signed prefixes

The root factors at omitted and decreasing positions are multiplied with the prescribed
simple representatives. Moving these representatives to the right conjugates each root
element by the representative of its preceding prefix.
-/

namespace SchubertGeometry
noncomputable section
open BruhatIntervals
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- The root element at a position uses the positive map at a decreasing step and the negative
map at an omitted step; an increasing step contributes the identity. -/
def deodharRootElement (parameters : Fin word.length → K) (j : Fin word.length) : G.points := by
  classical
  exact if j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    ReductiveGroups.gaParameterPoint (G.simpleRootMap word[j.val]) (parameters j)
  else if j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    ReductiveGroups.gaParameterPoint (G.negativeSimpleRootMap word[j.val]) (parameters j)
  else 1

/-- The simple representative is the inverse of the rank-one point x(1)y(-1)x(1). -/
def simpleRepresentative (i : G.rootBase.support) : G.points :=
  (G.reflectionPoint (i : G.rootIndex))⁻¹

/-- The signed simple representative is inverse at a decreasing step, trivial at an omitted
step, and the chosen simple representative at an increasing step. -/
def subwordStepPoint (j : Fin word.length) : G.points := by
  classical
  exact if j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    (simpleRepresentative G word[j.val])⁻¹
  else if j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then 1
  else simpleRepresentative G word[j.val]

/-- The Deodhar factor at one position is its root element followed by its signed representative. -/
def deodharStep (parameters : Fin word.length → K) (j : Fin word.length) : G.points :=
  deodharRootElement G expression parameters j * subwordStepPoint G expression j

/-- The signed representative of a subexpression prefix is the ordered product of its steps. -/
def subwordRepresentative (n : ℕ) : G.points :=
  ((List.ofFn (subwordStepPoint G expression)).take n).prod

/-- The Deodhar element of a prefix is the ordered product of its coordinate factors. -/
def deodharPrefix (parameters : Fin word.length → K) (n : ℕ) : G.points :=
  ((List.ofFn (deodharStep G expression parameters)).take n).prod


end
end SchubertGeometry
