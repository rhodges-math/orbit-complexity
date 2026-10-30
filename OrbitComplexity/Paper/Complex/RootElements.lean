import OrbitComplexity.SchubertGeometry.Roots.Elements
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Root elements and Weyl representatives over the complex numbers -/

noncomputable section
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti SchubertGeometry
open scoped CategoryTheory.MonObj
namespace SchubertOrbits.RootElements
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The root-element and torus formulas use one family of parameters. -/
def rootElementsAndTorus : Prop :=
  ∃ X Y : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K,
    IsRootElementSystem G X Y ∧
    ∀ (r : G.rootIndex) (t : (torusVariety G).points) (a : K),
      (torusPointsMulEquiv G t : G.points) * gaParameterPoint (X r) a =
        gaParameterPoint (X r) (torusWeightCharacter G (G.rootCharacter r).toAdd t * a) *
          (torusPointsMulEquiv G t : G.points)

end SchubertOrbits.RootElements

namespace SchubertOrbits
universe u

/-- Root elements satisfy the simple matrix and representative formulas. -/
theorem root_elements {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) : RootElements.rootElementsAndTorus G :=
  SchubertGeometry.root_elements_and_torus G

/-- Complex root elements satisfy the simple matrix and representative formulas. -/
theorem root_elements_complex (G : ReductiveGroupData ℂ) :
    RootElements.rootElementsAndTorus G :=
  root_elements G

end SchubertOrbits
