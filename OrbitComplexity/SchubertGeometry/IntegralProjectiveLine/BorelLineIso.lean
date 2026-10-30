import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import Batteries.Tactic.Lint

/-! # The simple Schubert projective line over an affine coefficient algebra -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
set_option autoImplicit false
noncomputable section
universe u
namespace SchubertGeometry
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The simple Schubert projective line after extension to an affine base. -/
def simpleBorelLineIso (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    ((algSpec (.of K)).obj (.op A) ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≅
        projectiveScheme A (ULift.{u} (Fin 2)) :=
  (Over.forget (Spec (.of K))).mapIso
      (tensorIso (Iso.refl ((algSpec (.of K)).obj (.op A))) (simpleSchubertIso G i)) ≪≫
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)).symm

end SchubertGeometry
