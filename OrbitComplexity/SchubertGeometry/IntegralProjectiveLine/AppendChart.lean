import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelLineIso
import Batteries.Tactic.Lint

/-! # Projective coordinates for a specified append chart -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v
namespace SchubertGeometry

/-- A specified product chart written in projective-line coordinates over its affine base. -/
def projectiveAppendChart {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    {V T : Over (Spec (.of K))}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T) :
    projectiveScheme A (ULift.{u} (Fin 2)) ⟶ T.left :=
  (simpleBorelLineIso G i A).inv ≫
    ((p ⊗ₘ 𝟙 (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c).left

end SchubertGeometry
