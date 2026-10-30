import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveAnchors
import OrbitComplexity.SchubertGeometry.Connectedness.ProjectiveCurveRetention

/-!
# Scalar endpoint maps for Richardson root curves

The zero and infinity sections, the root curve, and their cell anchors form
commuting triangles between the specified generic scalar models.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting GroupActions ReductiveGroups

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem section_from_ambient {T : Type*} [Category T] {B : T}
    {X F : Over B} (j : X ⟶ F) (p : Over.mk (𝟙 B) ⟶ F)
    (a : B ⟶ X.left) (h : a ≫ j.left = p.left) : a ≫ X.hom = 𝟙 B := by
  rw [← j.w, ← Category.assoc, h, p.w]
  rfl

private theorem section_left {T : Type*} [Category T] {B : T} {X : Over B}
    {v : Over.mk (𝟙 B) ⟶ X} {a : B ⟶ X.left} {ha : a ≫ X.hom = 𝟙 B}
    (hv : v = Over.homMk a ha) : v.left = a := by
  subst v
  rfl

private def unit_arrow {T : Type*} [Category T] {B : T} (U : Over B) :
    U ⟶ Over.mk (𝟙 B) := Over.homMk U.hom (Category.comp_id _)

private def point_arrow {T : Type*} [Category T] {B : T} (U : Over B)
    {X Y : Over B} (e : X ≅ Y) (p : Over.mk (𝟙 B) ⟶ X) : U ⟶ Y :=
  unit_arrow U ≫ p ≫ e.hom

private theorem conjugate_triangle {T : Type*} [Category T] {B : T}
    (U : Over B) {P P' D D' : Over B} (E : P ≅ P') (F : D ≅ D')
    (p : Over.mk (𝟙 B) ⟶ P) (c : P ⟶ D) (v : Over.mk (𝟙 B) ⟶ D)
    {a : B ⟶ D.left} (hv : v.left = a) (he : p.left ≫ c.left = a)
    {s' : U ⟶ P'} (hs : s' = point_arrow U E p)
    {c' : P' ⟶ D'} (hc : c' = E.inv ≫ c ≫ F.hom)
    {a' : U ⟶ D'} (ha : a' = point_arrow U F v) : s' ≫ c' = a' := by
  have hp : p ≫ c = v := Over.OverMorphism.ext (he.trans hv.symm)
  subst s' c' a'
  simp only [point_arrow, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc p c F.hom, hp]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- A cell anchor as a morphism over the base field. -/
def cellAnchorOver (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ (richardsonVariety G a b).toOver :=
  Over.homMk (cellRichardsonAnchor G a b w hne)
    (section_from_ambient (richardsonInclusion G a b)
      ((flagVariety G).pointsEquivOverHom (weylFlagPoint G w)) _
      (cellRichardsonAnchor_flag G a b w hne))

/-- The zero or infinity point, according to the Boolean index, over the field. -/
def rootEndpointPoint (ε : Bool) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))) :=
  if ε then
    (projectiveVariety K (ULift.{u} (Fin 2))).pointsEquivOverHom
      (Variety.mapPoints (projectiveLineChart K ⟨1⟩) (additivePointsEquiv K 0))
  else
    (projectiveVariety K (ULift.{u} (Fin 2))).pointsEquivOverHom
      (Variety.mapPoints (projectiveLineChart K ⟨0⟩) (additivePointsEquiv K 0))

/-- The specified projective endpoint on the generic scalar model. -/
def rootEndpointGenericMap (S : Subalgebra ℤ K) (ε : Bool) :
    genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) :=
  point_arrow _ (projectiveGenericIso S (ULift.{u} (Fin 2))) (rootEndpointPoint (K := K) ε)

/-- The cell anchor in a chosen Cartesian generic model of the Richardson target. -/
def cellAnchorGenericMap (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (S : Subalgebra ℤ K) (D : Over (Spec (.of S)))
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    genericScalarModel S (𝟙 (Spec (.of S))) ⟶ genericScalarModel S D.hom :=
  point_arrow _ (cartesianGenericIso S D (richardsonVariety G a b).toOver qD hD)
    (cellAnchorOver G a b w hne)

/-- The zero endpoint triangle commutes on the specified generic scalar models. -/
theorem rootCurve_zero_triangle (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b)
    (hne : Nonempty (cellIntersection G a b x).left)
    (S : Subalgebra ℤ K) (D : Over (Spec (.of S)))
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    rootEndpointGenericMap S false ≫
      projectiveGenericMap S (ULift.{u} (Fin 2)) D (richardsonVariety G a b).toOver qD hD
        (rootCurveRichardson G w i a x b hroot hpos hax hxy hyb) =
      cellAnchorGenericMap G a b x hne S D qD hD :=
  conjugate_triangle _ _ _ _ _ _
    (section_left (v := cellAnchorOver G a b x hne) rfl)
    (rootCurve_zero_anchor G w i a x b hroot hpos hax hxy hyb hne) rfl rfl rfl

/-- The infinity endpoint triangle commutes on the specified generic scalar models. -/
theorem rootCurve_infinity_triangle (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b)
    (hne : Nonempty (cellIntersection G a b (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x)).left)
    (S : Subalgebra ℤ K) (D : Over (Spec (.of S)))
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    rootEndpointGenericMap S true ≫
      projectiveGenericMap S (ULift.{u} (Fin 2)) D (richardsonVariety G a b).toOver qD hD
        (rootCurveRichardson G w i a x b hroot hpos hax hxy hyb) =
      cellAnchorGenericMap G a b (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) hne S D qD hD :=
  conjugate_triangle _ _ _ _ _ _
    (section_left (v := cellAnchorOver G a b (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) hne) rfl)
    (rootCurve_infinity_anchor G w i a x b hroot hpos hax hxy hyb hne) rfl rfl rfl

end SchubertGeometry.CellContraction
