import OrbitComplexity.SchubertGeometry.ProjectiveLine.Charts
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoConnected
import OrbitComplexity.SchubertGeometry.Deodhar.CellParameterPoints
import OrbitComplexity.SchubertGeometry.Parabolics.BruhatClosure
import OrbitComplexity.GroupActions.Actions.Translations

/-! # Translated simple Schubert curves

The intersection of an ascending translated simple curve with a containing Schubert
variety has connected underlying space.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)

private abbrev simpleFibre : Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

/-- The simple Schubert curve translated by a Weyl representative. -/
def simpleSchubertCurve :
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
      (flagVariety G).toOver :=
  schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) ≫
    Variety.translateMorphism (reductiveVariety G) (flagVariety G)
      (reductivePointsMulEquiv G (G.weylPoint w))

private theorem chart_points_cover (q : (simpleFibre G i).points) :
    (∃ t : K, Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K t) = q) ∨
      Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0) = q := by
  have hc : (simpleFibre G i).pointMap q ∈ Set.range (simplePositiveChart G i).left ∪
      Set.range (simpleNegativeChart G i).left := by
    rw [simpleCharts_cover G i]
    trivial
  rcases hc with hc | hc
  · left
    have hm : q ∈ Set.range (Variety.mapPoints (simplePositiveChart G i)) := by
      rw [Variety.range_mapPoints]
      exact hc
    obtain ⟨a, ha⟩ := hm
    obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
    exact ⟨t, ha⟩
  · have hm : q ∈ Set.range (Variety.mapPoints (simpleNegativeChart G i)) := by
      rw [Variety.range_mapPoints]
      exact hc
    obtain ⟨a, ha⟩ := hm
    obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
    by_cases ht : t = 0
    · exact Or.inr (ht ▸ ha)
    · left
      refine ⟨t⁻¹, ?_⟩
      have he := simpleCharts_transition G i (inv_ne_zero ht)
      simp only [inv_inv] at he
      exact he.trans ha

private theorem curve_positive_points (t : K) :
    Variety.mapPoints (simplePositiveChart G i ≫ simpleSchubertCurve G w i)
      (additivePointsEquiv K t) = flagVarietyPointsEquiv G (flagProjection G
        (G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
          (G.reflectionPoint i.val)⁻¹)) := by
  rw [simpleSchubertCurve, ← Category.assoc, Variety.mapPoints_comp,
    simplePositiveChart_points, Variety.mapPoints_translateMorphism,
    flagVarietyAction_points, ← flagProjection_smul]
  simp only [mul_assoc]

private theorem curve_zero_points :
    Variety.mapPoints (simpleNegativeChart G i ≫ simpleSchubertCurve G w i)
      (additivePointsEquiv K 0) = weylFlagPoint G w := by
  rw [simpleSchubertCurve, ← Category.assoc, Variety.mapPoints_comp,
    simpleNegativeChart_points, gaParameterPoint_zero,
    Variety.mapPoints_translateMorphism, flagVarietyAction_points,
    ← flagProjection_smul, mul_one]
  rfl

private theorem curve_positive_cell
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i)) (t : K) :
    Variety.mapPoints (simplePositiveChart G i ≫ simpleSchubertCurve G w i)
      (additivePointsEquiv K t) ∈ Set.range (Variety.mapPoints
        (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i))) := by
  let p : (schubertUnipotent G w).points := (schubertUnipotentPointsEquiv G w).symm 1
  let q := (rankOneGaProductPointsEquiv G w).symm (p, additivePointsEquiv K t)
  refine ⟨Variety.mapPoints (rankOneGaCellIso G w i hw).hom q, ?_⟩
  rw [← Variety.mapPoints_comp, rankOneGaCellIso_ambient_points G w i hw p t,
    curve_positive_points G w i t]
  simp only [p, MulEquiv.apply_symm_apply, OneMemClass.coe_one, one_mul]

private theorem cell_mem_lower {a v : G.weylGroup} {q : (flagVariety G).points}
    (hq : q ∈ Set.range (Variety.mapPoints (schubertCellInclusion G a))) :
    q ∈ Set.range (Variety.mapPoints (schubertInclusion G v)) ↔
      WeylBruhatLE G.rootBase a v := by
  rw [schubertVariety_points_cells]
  constructor
  · intro hv
    obtain ⟨b, hb, hqb⟩ := Set.mem_iUnion₂.mp hv
    rw [schubertCell_points_range] at hq hqb
    exact schubertOrbits_disjoint G hq hqb ▸ hb
  · intro hav
    exact Set.mem_iUnion₂.mpr ⟨a, hav, hq⟩

private abbrev zeroPoint : (simpleFibre G i).points :=
  Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0)

private theorem curve_zero_mem (v : G.weylGroup) (hwv : WeylBruhatLE G.rootBase w v) :
    Variety.mapPoints (simpleSchubertCurve G w i) (zeroPoint G i) ∈
      Set.range (Variety.mapPoints (schubertInclusion G v)) := by
  change Variety.mapPoints (simpleSchubertCurve G w i)
    (Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0)) ∈ _
  rw [← Variety.mapPoints_comp, curve_zero_points, weylFlag_mem_schubert_iff]
  exact hwv

private theorem curve_mem_lower (v : G.weylGroup)
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
    (hwv : WeylBruhatLE G.rootBase w v) (q : (simpleFibre G i).points) :
    Variety.mapPoints (simpleSchubertCurve G w i) q ∈
      Set.range (Variety.mapPoints (schubertInclusion G v)) ↔
        WeylBruhatLE G.rootBase (w * RootPairing.weylGroup.ofIdx G.rootSystem i) v ∨
          q = zeroPoint G i := by
  constructor
  · intro hq
    rcases chart_points_cover G i q with ⟨t, ht⟩ | ht
    · left
      rw [← ht, ← Variety.mapPoints_comp] at hq
      exact (cell_mem_lower G (curve_positive_cell G w i hw t)).mp hq
    · exact Or.inr ht.symm
  · rintro (hlong | rfl)
    · rcases chart_points_cover G i q with ⟨t, ht⟩ | ht
      · rw [← ht, ← Variety.mapPoints_comp]
        exact (cell_mem_lower G (curve_positive_cell G w i hw t)).mpr hlong
      · rw [← ht]
        exact curve_zero_mem G w i v hwv
    · exact curve_zero_mem G w i v hwv

omit [CharZero K] in
private theorem closed_eq_of_points (X : Variety K) (S T : Set X.scheme)
    (hS : IsClosed S) (hT : IsClosed T) (h : X.pointMap ⁻¹' S = X.pointMap ⁻¹' T) :
    S = T := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  have he : S ∩ closedPoints X.scheme = T ∩ closedPoints X.scheme := by
    rw [← X.pointMap_range, ← Set.image_preimage_eq_inter_range,
      ← Set.image_preimage_eq_inter_range, h]
  exact (closure_inter_closedPoints hS).symm.trans
    ((congrArg closure he).trans (closure_inter_closedPoints hT))

/-- A Schubert intersection in the ascending simple curve has full or singleton support. -/
theorem simpleCurve_image_cases (v : G.weylGroup)
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
    (hwv : WeylBruhatLE G.rootBase w v) :
    (simpleSchubertCurve G w i).left ⁻¹' Set.range (schubertInclusion G v).left =
      Set.univ ∨
    (simpleSchubertCurve G w i).left ⁻¹' Set.range (schubertInclusion G v).left =
      {(schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).pointMap
        (Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0))} := by
  let S := (simpleSchubertCurve G w i).left ⁻¹' Set.range (schubertInclusion G v).left
  have hS : IsClosed S :=
    (schubertInclusion G v).left.isClosedMap.isClosed_range.preimage
      (simpleSchubertCurve G w i).left.continuous
  have hmem (q : (simpleFibre G i).points) :
      (simpleFibre G i).pointMap q ∈ S ↔
        WeylBruhatLE G.rootBase (w * RootPairing.weylGroup.ofIdx G.rootSystem i) v ∨
          q = zeroPoint G i := by
    change (simpleSchubertCurve G w i).left ((simpleFibre G i).pointMap q) ∈
      Set.range (schubertInclusion G v).left ↔ _
    rw [← Variety.pointMap_mapPoints]
    change Variety.mapPoints (simpleSchubertCurve G w i) q ∈
      (flagVariety G).pointMap ⁻¹' Set.range (schubertInclusion G v).left ↔ _
    rw [← Variety.range_mapPoints]
    exact curve_mem_lower G w i v hw hwv q
  by_cases hlong : WeylBruhatLE G.rootBase
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i) v
  · left
    apply closed_eq_of_points (simpleFibre G i) S Set.univ hS isClosed_univ
    ext q
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact (hmem q).mpr (Or.inl hlong)
  · right
    apply closed_eq_of_points (simpleFibre G i) S _ hS
      ((simpleFibre G i).pointsEquivClosedPoints (zeroPoint G i)).property
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hmem]
    simp only [hlong, false_or]
    change q = zeroPoint G i ↔ (simpleFibre G i).pointMap q =
      (simpleFibre G i).pointMap (zeroPoint G i)
    exact (simpleFibre G i).pointMap_injective.eq_iff.symm

/-- Intersecting the ascending simple curve with a containing Schubert variety is connected. -/
theorem simpleCurve_intersection_connected (v : G.weylGroup)
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
    (hwv : WeylBruhatLE G.rootBase w v) :
    ConnectedSpace
      (pullback (simpleSchubertCurve G w i).left (schubertInclusion G v).left : Scheme.{u}) := by
  let f := pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  have he : Set.range f =
      (simpleSchubertCurve G w i).left ⁻¹' Set.range (schubertInclusion G v).left :=
    Scheme.Pullback.range_fst _ _
  have hconn : _root_.IsConnected (Set.range f) := by
    rw [he]
    rcases simpleCurve_image_cases G w i v hw hwv with h | h
    · rw [h]
      have : IsIntegral (simpleFibre G i).scheme :=
        GeometricallyIntegral.isIntegral_of_subsingleton (simpleFibre G i).toSpec
      have : ConnectedSpace (simpleFibre G i).scheme := inferInstance
      exact isConnected_univ (α := (simpleFibre G i).scheme)
    · rw [h]
      exact isConnected_singleton
  have : ConnectedSpace (Set.range f) := isConnected_iff_connectedSpace.mp hconn
  exact f.isEmbedding.toHomeomorph.connectedSpace_iff.mpr inferInstance

end SchubertGeometry
