import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellContractionScheme
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveContainment

/-!
# Root-curve endpoints and cell anchors

The two rational endpoints of a reflection-root curve agree with the origins of
its endpoint cell intersections, as morphisms to the Richardson variety.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem point_map_equation {K : Type u} [Field K]
    {P F : GroupActions.Variety K} {d : P.toOver ⟶ F.toOver}
    {p : P.points} {q : F.points} (h : GroupActions.Variety.mapPoints d p = q) :
    (P.pointsEquivOverHom p).left ≫ d.left = (F.pointsEquivOverHom q).left := by
  subst q
  rfl

private theorem over_comp_equation {T : Type*} [Category T] {B : T}
    {P X F : Over B} {c : P ⟶ X} {j : X ⟶ F} {d : P ⟶ F}
    (h : c ≫ j = d) : c.left ≫ j.left = d.left :=
  congrArg Over.Hom.left h

private theorem anchor_equation {K : Type u} [Field K]
    {P X F : GroupActions.Variety K} {c : P.toOver ⟶ X.toOver}
    {j : X.toOver ⟶ F.toOver} [Mono j.left] {d : P.toOver ⟶ F.toOver}
    (hc : c ≫ j = d) {p : P.points} {q : F.points}
    (hp : GroupActions.Variety.mapPoints d p = q)
    (v : Spec (.of K) ⟶ X.scheme)
    (hv : v ≫ j.left = (F.pointsEquivOverHom q).left) :
    (P.pointsEquivOverHom p).left ≫ c.left = v := by
  apply (cancel_mono j.left).mp
  rw [Category.assoc, over_comp_equation hc, point_map_equation hp, hv]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The zero endpoint of the Richardson-valued root curve is its first cell anchor. -/
theorem rootCurve_zero_anchor (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b)
    (hne : Nonempty (cellIntersection G a b x).left) :
    ((projectiveVariety K (ULift.{u} (Fin 2))).pointsEquivOverHom
      (GroupActions.Variety.mapPoints (projectiveLineChart K ⟨0⟩)
        (additivePointsEquiv K 0))).left ≫
        (rootCurveRichardson G w i a x b hroot hpos hax hxy hyb).left =
      cellRichardsonAnchor G a b x hne :=
  anchor_equation (rootCurveRichardson_comp G w i a x b hroot hpos hax hxy hyb)
    (rootCurveProjective_at_zero G w i x hpos) _
    (cellRichardsonAnchor_flag G a b x hne)

/-- The infinity endpoint of the root curve is its reflected cell anchor. -/
theorem rootCurve_infinity_anchor (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b)
    (hne : Nonempty (cellIntersection G a b (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x)).left) :
    ((projectiveVariety K (ULift.{u} (Fin 2))).pointsEquivOverHom
      (GroupActions.Variety.mapPoints (projectiveLineChart K ⟨1⟩)
        (additivePointsEquiv K 0))).left ≫
        (rootCurveRichardson G w i a x b hroot hpos hax hxy hyb).left =
      cellRichardsonAnchor G a b (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * x) hne :=
  anchor_equation (rootCurveRichardson_comp G w i a x b hroot hpos hax hxy hyb)
    (rootCurveProjective_at_infinity G w i x hpos) _
    (cellRichardsonAnchor_flag G a b _ hne)

end SchubertGeometry.CellContraction
