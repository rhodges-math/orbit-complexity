import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveGluing
import OrbitComplexity.SchubertGeometry.Connectedness.ReflectionCurves
import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.SchubertGeometry.Cells.OppositeClosure
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositeTangent

/-! # Root curves inside Richardson varieties

Positive and negative root parameters lie in the corresponding Borel groups. Their
orbit charts therefore lie in the required Schubert supports. The reciprocal chart
identity and the two Weyl endpoint bounds give the remaining chart containments.
-/

noncomputable section

namespace SchubertGeometry

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti

universe u

private theorem negative_transport {I : Type*} (P : I → Prop)
    (f n : I → I) (hn : ∀ j, P (n j) ↔ ¬ P j) {i j : I}
    (he : n i = j) (hc : f (n i) = n (f i)) (hp : P (f i)) : ¬ P (f j) := by
  rw [← he, hc]
  exact fun h => (hn _).mp h hp

private theorem over_comp_eq {C : Type*} [Category C] {B : C}
    {X Y Z : Over B} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (he : f ≫ g = h) : f.left ≫ g.left = h.left :=
  (Over.comp_left X Y Z f g).symm.trans (congrArg Over.Hom.left he)

private theorem over_factor_exists {C : Type*} [Category C] {B : C}
    {X Y Z : Over B} (p : X ⟶ Z) (i : Y ⟶ Z)
    (g : X.left ⟶ Y.left) (h : g ≫ i.left = p.left) :
    ∃ q : X ⟶ Y, q ≫ i = p := by
  have hg : g ≫ Y.hom = X.hom := by
    calc
      _ = g ≫ i.left ≫ Z.hom := congrArg (fun k => g ≫ k) i.w.symm
      _ = p.left ≫ Z.hom := by rw [← Category.assoc, h]
      _ = _ := p.w
  refine ⟨Over.homMk g hg, ?_⟩
  apply Over.OverMorphism.ext
  exact h

/-- Range containment can be checked on two covering charts, with the maps kept abstract. -/
theorem rootCurve_range_pair {A X Y : Scheme} (c₀ c₁ : A ⟶ X) (f : X ⟶ Y)
    (d₀ d₁ : A ⟶ Y) (hcover : Set.range c₀ ∪ Set.range c₁ = Set.univ)
    (h₀ : c₀ ≫ f = d₀) (h₁ : c₁ ≫ f = d₁) (S : Set Y)
    (hd₀ : Set.range d₀ ⊆ S) (hd₁ : Set.range d₁ ⊆ S) : Set.range f ⊆ S := by
  rintro z ⟨p, rfl⟩
  have hp : p ∈ Set.range c₀ ∪ Set.range c₁ := by rw [hcover]; trivial
  rcases hp with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · change (c₀ ≫ f) a ∈ S
    rw [h₀]
    exact hd₀ ⟨a, rfl⟩
  · change (c₁ ≫ f) a ∈ S
    rw [h₁]
    exact hd₁ ⟨a, rfl⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- A positive-weight additive parameter lies in the chosen Borel over every value algebra. -/
theorem rootCurve_parameter_borel
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) (r : G.rootIndex)
    (hφ : gaAffineGroupTangent φ ∈ G.rootWeightSpace r) (hr : G.rootBase.IsPos r)
    {A : Type*} [CommRing A] [Algebra K A] (a : A) :
    gaParameterPoint φ a ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal (CommAlgCat.of K A) :=
  GaParameterPoint.mem_of_tangent_mem_quotient φ G.borelIdeal
    ((G.rootWeightSpace_le_borel r).mpr hr hφ) a

/-- A negative-weight additive parameter lies in the opposite Borel on rational points. -/
theorem rootCurve_parameter_opposite
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) (r : G.rootIndex)
    (hφ : gaAffineGroupTangent φ ∈ G.rootWeightSpace r) (hr : ¬ G.rootBase.IsPos r)
    (t : K) : gaParameterPoint φ t ∈ G.oppositeBorelPoints := by
  apply G.oppositeUnipotent_le_oppositeBorel
  apply GaParameterPoint.mem_of_tangent_mem_quotient φ G.oppositeUnipotentIdeal
  change gaAffineGroupTangent φ ∈ G.oppositeUnipotentTangent.toSubmodule
  rw [G.oppositeUnipotentTangent_eq_sum]
  have hle : G.rootWeightSpace r ≤
      ⨆ (j : G.rootIndex) (_ : ¬ G.rootBase.IsPos j), G.rootWeightSpace j :=
    le_iSup₂_of_le r hr le_rfl
  exact hle hφ

private theorem lowerRoot_negative (w : G.weylGroup) (i : G.rootBase.support)
    (hpos : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val)) :
    ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w (-i.val)) := by
  exact negative_transport G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w)
    (fun r => G.rootSystem.reflectionPerm r r) (isPos_neg_index_iff G.rootBase)
    (LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg (H := G.cartan) i.val)
    (weylGroupToPerm_neg_index w i.val) hpos

private theorem weylFlag_opposite (a x : G.weylGroup)
    (hax : WeylBruhatLE G.rootBase a x) :
    weylFlagPoint G x ∈ Set.range (Variety.mapPoints (oppositeSchubertInclusion G a)) := by
  rw [oppositeSchubert_points_cells]
  apply Set.mem_iUnion₂.mpr
  refine ⟨x, hax, ?_⟩
  rw [oppositeSchubertCell_points_range]
  exact MulAction.mem_orbit_self _

private theorem borel_flag_stable (b : G.points) (hb : b ∈ G.borelPoints)
    (x v : G.weylGroup) (hxv : WeylBruhatLE G.rootBase x v) :
    flagVarietyPointsEquiv G (b • flagProjection G (G.weylPoint x)) ∈
      Set.range (Variety.mapPoints (schubertInclusion G v)) := by
  let q := (borelPointsMulEquiv G).symm ⟨b, hb⟩
  have he : q • weylFlagPoint G x =
      flagVarietyPointsEquiv G (b • flagProjection G (G.weylPoint x)) := by
    change (borelPointsMulEquiv G).symm ⟨b, hb⟩ •
      flagVarietyPointsEquiv G (flagProjection G (G.weylPoint x)) = _
    rw [borelFlag_smul, MulEquiv.apply_symm_apply]
  rw [← he]
  exact schubertVariety_stable G v q ((weylFlag_mem_schubert_iff G x v).mpr hxv)

private theorem opposite_flag_stable (b : G.points) (hb : b ∈ G.oppositeBorelPoints)
    (a x : G.weylGroup) (hax : WeylBruhatLE G.rootBase a x) :
    flagVarietyPointsEquiv G (b • flagProjection G (G.weylPoint x)) ∈
      Set.range (Variety.mapPoints (oppositeSchubertInclusion G a)) := by
  let q := (oppositeBorelPointsMulEquiv G).symm ⟨b, hb⟩
  have he : q • weylFlagPoint G x =
      flagVarietyPointsEquiv G (b • flagProjection G (G.weylPoint x)) := by
    change (oppositeBorelPointsMulEquiv G).symm ⟨b, hb⟩ •
      flagVarietyPointsEquiv G (flagProjection G (G.weylPoint x)) = _
    rw [oppositeBorelFlag_smul, MulEquiv.apply_symm_apply]
  rw [← he]
  exact oppositeSchubertVariety_stable G a q (weylFlag_opposite G a x hax)

private theorem upperChart_in_schubert (w : G.weylGroup) (i : G.rootBase.support)
    (y b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hyb : WeylBruhatLE G.rootBase y b) :
    Set.range (Variety.mapPoints (rootCurveInfinityChart G w i y)) ⊆
      Set.range (Variety.mapPoints (schubertInclusion G b)) := by
  rintro z ⟨p, rfl⟩
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  rw [rootCurve_infinityChart_points]
  exact borel_flag_stable G _
    (rootCurve_parameter_borel G _ _ (rootUpperMap_tangent G w i) hroot t) y b hyb

private theorem lowerChart_in_opposite (w : G.weylGroup) (i : G.rootBase.support)
    (a x : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hax : WeylBruhatLE G.rootBase a x) :
    Set.range (Variety.mapPoints (rootCurveZeroChart G w i x)) ⊆
      Set.range (Variety.mapPoints (oppositeSchubertInclusion G a)) := by
  rintro z ⟨p, rfl⟩
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  rw [rootCurve_zeroChart_points]
  exact opposite_flag_stable G _
    (rootCurve_parameter_opposite G _ _ (rootLowerMap_tangent G w i)
      (lowerRoot_negative G w i hroot) t) a x hax

private theorem lowerChart_in_schubert (w : G.weylGroup) (i : G.rootBase.support)
    (x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val)))
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b) :
    Set.range (Variety.mapPoints (rootCurveZeroChart G w i x)) ⊆
      Set.range (Variety.mapPoints (schubertInclusion G b)) := by
  rintro z ⟨p, rfl⟩
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  by_cases ht : t = 0
  · subst t
    rw [rootCurve_zeroChart_zero]
    exact (weylFlag_mem_schubert_iff G x b).mpr (hxy.trans hyb)
  · rw [rootCurve_charts_transition G w i x hpos ht]
    exact upperChart_in_schubert G w i _ b hroot hyb ⟨_, rfl⟩

private theorem upperChart_in_opposite (w : G.weylGroup) (i : G.rootBase.support)
    (a x : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x)) :
    Set.range (Variety.mapPoints (rootCurveInfinityChart G w i
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * x))) ⊆
      Set.range (Variety.mapPoints (oppositeSchubertInclusion G a)) := by
  rintro z ⟨p, rfl⟩
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  by_cases ht : t = 0
  · subst t
    rw [rootCurve_infinityChart_zero]
    exact weylFlag_opposite G a _ (hax.trans hxy)
  · have he := rootCurve_charts_transition G w i x hpos (inv_ne_zero ht)
    rw [inv_inv] at he
    rw [← he]
    exact lowerChart_in_opposite G w i a x hroot hax ⟨_, rfl⟩

/-- The global root curve is contained in every Schubert variety bounding its upper endpoint. -/
theorem rootCurve_schubert_range (w : G.weylGroup) (i : G.rootBase.support)
    (x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val)))
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b) :
    Set.range (rootCurveProjective G w i x hpos).left ⊆
      Set.range (schubertInclusion G b).left := by
  apply rootCurve_range_pair (projectiveLineChart K ⟨0⟩).left
    (projectiveLineChart K ⟨1⟩).left (rootCurveProjective G w i x hpos).left
    (rootCurveZeroChart G w i x).left
    (rootCurveInfinityChart G w i (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x)).left (projectiveLineChart_cover K)
    (over_comp_eq (rootCurveProjective_zero G w i x hpos))
    (over_comp_eq (rootCurveProjective_infinity G w i x hpos))
  · exact Variety.range_subset_of_mapPoints _ _
      (lowerChart_in_schubert G w i x b hroot hpos hxy hyb)
  · exact Variety.range_subset_of_mapPoints _ _
      (upperChart_in_schubert G w i _ b hroot hyb)

/-- The global root curve is contained in every opposite Schubert variety bounding its lower end. -/
theorem rootCurve_opposite_range (w : G.weylGroup) (i : G.rootBase.support)
    (a x : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x)) :
    Set.range (rootCurveProjective G w i x hpos).left ⊆
      Set.range (oppositeSchubertInclusion G a).left := by
  apply rootCurve_range_pair (projectiveLineChart K ⟨0⟩).left
    (projectiveLineChart K ⟨1⟩).left (rootCurveProjective G w i x hpos).left
    (rootCurveZeroChart G w i x).left
    (rootCurveInfinityChart G w i (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x)).left (projectiveLineChart_cover K)
    (over_comp_eq (rootCurveProjective_zero G w i x hpos))
    (over_comp_eq (rootCurveProjective_infinity G w i x hpos))
  · exact Variety.range_subset_of_mapPoints _ _
      (lowerChart_in_opposite G w i a x hroot hax)
  · exact Variety.range_subset_of_mapPoints _ _
      (upperChart_in_opposite G w i a x hroot hpos hax hxy)

private theorem rootCurveRichardson_exists (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b) :
    ∃ f : (projectiveVariety K (ULift.{u} (Fin 2))).toOver ⟶
      (richardsonVariety G a b).toOver,
      f ≫ richardsonInclusion G a b = rootCurveProjective G w i x hpos := by
  let : IsReduced (projectiveVariety K (ULift.{u} (Fin 2))).toOver.left :=
    (projectiveVariety K (ULift.{u} (Fin 2))).reduced
  exact over_factor_exists (rootCurveProjective G w i x hpos) (richardsonInclusion G a b)
    (richardsonCurveFactor G a b _
      (rootCurve_schubert_range G w i x b hroot hpos hxy hyb)
      (rootCurve_opposite_range G w i a x hroot hpos hax hxy))
    (richardsonCurveFactor_comp G a b _ _ _)

/-- The arbitrary-root projective curve factors through the Richardson variety of its bounds. -/
def rootCurveRichardson (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b) :
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver ⟶ (richardsonVariety G a b).toOver :=
  (rootCurveRichardson_exists G w i a x b hroot hpos hax hxy hyb).choose

/-- The Richardson factor retains the specified ambient root curve. -/
theorem rootCurveRichardson_comp (w : G.weylGroup) (i : G.rootBase.support)
    (a x b : G.weylGroup) (hroot : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm w i.val)) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (hax : WeylBruhatLE G.rootBase a x)
    (hxy : WeylBruhatLE G.rootBase x (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x))
    (hyb : WeylBruhatLE G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * x) b) :
    rootCurveRichardson G w i a x b hroot hpos hax hxy hyb ≫ richardsonInclusion G a b =
      rootCurveProjective G w i x hpos :=
  (rootCurveRichardson_exists G w i a x b hroot hpos hax hxy hyb).choose_spec

-- CoverRoots supplies the intrinsic Bruhat-cover root and its positive simple Weyl
-- presentation; it applies this lower-level producer without a cyclic import here.
-- GAP: C6-STAGE. RootCurveRetention descends the global factored maps into
-- the same target model. Retain their anchor endpoint equations jointly with
-- the covering-source equations. No claim about arbitrary nonreduced arithmetic
-- fibres is inferred from their rational points in this file.

end SchubertGeometry
