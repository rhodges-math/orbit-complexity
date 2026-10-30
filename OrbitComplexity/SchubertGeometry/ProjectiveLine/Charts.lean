import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.SchubertGeometry.Parabolics.LeviStability
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviSimple
import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.SchubertGeometry.ProjectiveLine.ChartsScaling
import OrbitComplexity.SchubertGeometry.Deodhar.RankOnePoints
import OrbitComplexity.SchubertGeometry.Deodhar.InitialCell
import OrbitComplexity.SchubertGeometry.Cells.OrbitDecomposition
import Batteries.Tactic.Lint

/-! # The two additive charts of a simple Schubert variety

The simple root parametrizes the open Schubert cell. Translation by the chosen
reflection in the rank-one Levi gives a second open chart. A nonzero scalar change
identifies that chart with the specified negative simple-root parameter.
The two charts cover every scheme point and have reciprocal transition parameter.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
private theorem exists_simple_conjugation_scale (i : G.rootBase.support) :
    ∃ c : K, c ≠ 0 ∧ ∀ t : K,
      G.reflectionPoint i.val * gaParameterPoint (G.simpleRootMap i) t *
        (G.reflectionPoint i.val)⁻¹ = gaParameterPoint (G.negativeSimpleRootMap i) (c * t) := by
  let n := G.reflectionPoint i.val
  let x := gaAffineGroupTangent (G.simpleRootMap i)
  let y := gaAffineGroupTangent (G.negativeSimpleRootMap i)
  have hm : affineGroupAdjointRepresentation n x ∈ G.rootWeightSpace (-i.val) := by
    have hmap := G.isBruhatSystem.weyl.transport_reflection i.val i.val
    change (G.rootWeightSpace i.val).map
      ((affineGroupAdjointLieEquiv n).toLinearEquiv : G.tangent →ₗ[K] G.tangent) =
        G.rootWeightSpace (G.rootSystem.reflectionPerm i.val i.val) at hmap
    rw [LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg] at hmap
    apply hmap.le
    exact Submodule.mem_map.mpr ⟨x, G.simpleRootMap_tangent_mem i, rfl⟩
  have hy0 : (⟨y, G.negativeRootMap_tangent_mem i⟩ : G.rootWeightSpace (-i.val)) ≠ 0 := by
    intro hz
    exact G.negativeRootMap_tangent_ne_zero i (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hy0).mp
    (G.rootWeightSpace_finrank (-i.val)) ⟨_, hm⟩
  have he : affineGroupAdjointRepresentation n x = c • y := (congrArg Subtype.val hc).symm
  have hc0 : c ≠ 0 := by
    intro hc0
    apply G.simpleRootMap_tangent_ne_zero i
    apply (affineGroupAdjointLieEquiv n).injective
    change affineGroupAdjointRepresentation n x = affineGroupAdjointRepresentation n 0
    rw [he, hc0]
    exact (zero_smul K y).trans (map_zero (affineGroupAdjointRepresentation n)).symm
  refine ⟨c, hc0, ?_⟩
  intro t
  exact GaAffineGroupPoints.conjugate_of_tangent_eq (G.simpleRootMap i)
    (G.negativeSimpleRootMap i) n c he t
private theorem singleton_descents (i : G.rootBase.support) :
    ({i} : Set G.rootBase.support) ⊆ BruhatIntervals.leftDescents
      (weylCoxeterSystem G.rootBase) (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  intro j hj
  have hji : j = i := Set.mem_singleton_iff.mp hj
  subst j
  change (weylCoxeterSystem G.rootBase).IsLeftDescent
    (RootPairing.weylGroup.ofIdx G.rootSystem i.val) i
  rw [← weylCoxeterSystem_simple G.rootBase i]
  change (weylCoxeterSystem G.rootBase).length
      ((weylCoxeterSystem G.rootBase).simple i * (weylCoxeterSystem G.rootBase).simple i) <
    (weylCoxeterSystem G.rootBase).length ((weylCoxeterSystem G.rootBase).simple i)
  rw [CoxeterSystem.simple_mul_simple_self, CoxeterSystem.length_one, CoxeterSystem.length_simple]
  exact Nat.zero_lt_one
private instance simpleLeviAction (i : G.rootBase.support) :
    ModObj (leviVariety G {i}).toOver
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver :=
  schubertLeviAction G {i} _ (singleton_descents G i)
private instance simpleLeviEquivariant (i : G.rootBase.support) :
    IsModHom (leviVariety G {i}).toOver
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :=
  schubertLeviEquivariant G {i} _ (singleton_descents G i)
section CellOpen
open Topology TopologicalSpace
omit [IsAlgClosed K] [CharZero K] in
private def locallyClosedToClosure (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) :
    (X.locallyClosedSubvariety S hS).toOver ⟶
      (X.closedSubvariety ⟨closure S, isClosed_closure⟩).toOver :=
  Variety.openInclusion _ _
omit [IsAlgClosed K] [CharZero K] in
private theorem locallyClosedToClosure_fac (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) :
    locallyClosedToClosure X S hS ≫ X.closedInclusion ⟨closure S, isClosed_closure⟩ =
      X.locallyClosedInclusion S hS := rfl
omit [IsAlgClosed K] [CharZero K] in
private theorem locallyClosedLift_isOpen (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) (Z : Closeds X.scheme)
    (hZ : Z = ⟨closure S, isClosed_closure⟩)
    (f : (X.locallyClosedSubvariety S hS).toOver ⟶ (X.closedSubvariety Z).toOver)
    (hf : f ≫ X.closedInclusion Z = X.locallyClosedInclusion S hS) :
    IsOpenImmersion f.left := by
  subst Z
  have he : f = locallyClosedToClosure X S hS := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (X.closedInclusion ⟨closure S, isClosed_closure⟩).left).mp
    exact congrArg Over.Hom.left (hf.trans (locallyClosedToClosure_fac X S hS).symm)
  rw [he]
  exact Variety.openInclusion_isOpenImmersion _ _
/-- The top Schubert cell includes as an open subvariety of its Schubert variety. -/
private instance cellOfLE_isOpen (w : G.weylGroup) :
    IsOpenImmersion (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w)).left := by
  apply locallyClosedLift_isOpen (flagVariety G)
    (Set.range (Variety.orbitMorphism (borelVariety G) (flagVariety G)
      (weylFlagPoint G w)).left)
    (orbitImage_locallyClosed (borelVariety G) (flagVariety G) (weylFlagPoint G w))
    (schubertSupport G w)
  · apply Closeds.ext
    exact congrArg closure (orbitInclusion_range (borelVariety G)
      (flagVariety G) (weylFlagPoint G w))
  · exact schubertCellOfLE_comp G w w _

end CellOpen

/-- The positive simple-root chart of the simple Schubert variety. -/
def simplePositiveChart (i : G.rootBase.support) :
    (additiveVariety K).toOver ⟶
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver :=
  (simpleCellIso G i).hom ≫ schubertCellOfLE G _ _ (WeylBruhatLE.refl G.rootBase _)
/-- The positive simple-root chart is an open immersion. -/
instance simplePositiveChart_isOpen (i : G.rootBase.support) :
    IsOpenImmersion (simplePositiveChart G i).left := by
  change IsOpenImmersion ((simpleCellIso G i).hom.left ≫
    (schubertCellOfLE G _ _ (WeylBruhatLE.refl G.rootBase _)).left)
  infer_instance
/-- The positive chart sends its parameter to the specified simple-cell flag. -/
theorem simplePositiveChart_points (i : G.rootBase.support) (t : K) :
    Variety.mapPoints (simplePositiveChart G i ≫
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
        (additivePointsEquiv K t) = flagVarietyPointsEquiv G
          (flagProjection G (gaParameterPoint (G.simpleRootMap i) t *
            (G.reflectionPoint i.val)⁻¹)) := by
  rw [simplePositiveChart, Category.assoc, schubertCellOfLE_comp]
  exact simpleCellIso_points G i t

private def reflectionLeviPoint (i : G.rootBase.support) : (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨G.reflectionPoint i.val, G.reflectionPoint_mem_levi {i} i (by simp)⟩
private theorem reflectionLeviPoint_coe (i : G.rootBase.support) :
    (leviPointsMulEquiv G {i} (reflectionLeviPoint G i) : G.points) =
      G.reflectionPoint i.val := by
  simp only [reflectionLeviPoint, MulEquiv.apply_symm_apply]
private def simpleConjugationScale (i : G.rootBase.support) : K :=
  (exists_simple_conjugation_scale G i).choose
private theorem simpleConjugationScale_ne (i : G.rootBase.support) :
    simpleConjugationScale G i ≠ 0 := (exists_simple_conjugation_scale G i).choose_spec.1
private theorem simpleConjugationScale_apply (i : G.rootBase.support) (t : K) :
    G.reflectionPoint i.val * gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹ =
      gaParameterPoint (G.negativeSimpleRootMap i) (simpleConjugationScale G i * t) :=
  (exists_simple_conjugation_scale G i).choose_spec.2 t

/-- The scalar-normalized reflection translate is the negative simple-root chart. -/
def simpleNegativeChart (i : G.rootBase.support) :
    (additiveVariety K).toOver ⟶
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver :=
  (additiveScaleIso (simpleConjugationScale G i)⁻¹
    (inv_ne_zero (simpleConjugationScale_ne G i))).hom ≫ simplePositiveChart G i ≫
      (Variety.translationIso (leviVariety G {i})
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
          (reflectionLeviPoint G i)).hom
/-- The negative simple-root chart is an open immersion. -/
instance simpleNegativeChart_isOpen (i : G.rootBase.support) :
    IsOpenImmersion (simpleNegativeChart G i).left := by
  change IsOpenImmersion (_ ≫ (simplePositiveChart G i).left ≫ _)
  infer_instance
omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_smul {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (t : H.points) (q : X.points) :
    Variety.mapPoints f (t • q) = t • Variety.mapPoints f q := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (t • q) ≫ f = Y.pointsEquivOverHom (t • Variety.mapPoints f q)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom t) (X.pointsEquivOverHom q)
/-- The negative chart retains the specified negative simple-root parameter. -/
theorem simpleNegativeChart_points (i : G.rootBase.support) (t : K) :
    Variety.mapPoints (simpleNegativeChart G i ≫
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
        (additivePointsEquiv K t) = flagVarietyPointsEquiv G
          (flagProjection G (gaParameterPoint (G.negativeSimpleRootMap i) t)) := by
  simp only [simpleNegativeChart, Variety.mapPoints_comp]
  rw [additiveScaleIso_points]
  simp only [Variety.translationIso]
  rw [Variety.mapPoints_translateMorphism]
  rw [equivariant_smul (H := leviVariety G {i}), leviFlag_smul,
    ← Variety.mapPoints_comp, simplePositiveChart_points, reflectionLeviPoint_coe,
    flagVarietyAction_points, ← flagProjection_smul, ← mul_assoc,
    simpleConjugationScale_apply]
  rw [mul_inv_cancel_left₀ (simpleConjugationScale_ne G i)]

private theorem lower_simple (i : G.rootBase.support) (w : G.weylGroup)
    (hw : WeylBruhatLE G.rootBase w (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :
    w = 1 ∨ w = RootPairing.weylGroup.ofIdx G.rootSystem i.val := by
  have hs : rootInversionCount G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val) = 1 := by
    rw [← weylCoxeterSystem_length, ← weylCoxeterSystem_simple]
    exact CoxeterSystem.length_simple _ i
  have hle := hw.length_le
  rcases Nat.eq_zero_or_pos (rootInversionCount G.rootBase w) with hz | hz
  · exact Or.inl ((rootInversionCount_eq_zero_iff G.rootBase w).mp hz)
  · exact Or.inr (hw.eq_of_length_eq (by omega))

/-- The negative chart followed by the flag inclusion is the negative root morphism. -/
theorem simpleNegativeChart_comp (i : G.rootBase.support) :
    simpleNegativeChart G i ≫
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
    gaMorphism G (G.negativeSimpleRootMap i) ≫ flagQuotientMorphism G := by
  apply Variety.mapPoints_injective
  funext p
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  rw [simpleNegativeChart_points, Variety.mapPoints_comp, gaMorphism_points,
    flagQuotientMorphism_points]
/-- The positive and negative parameters on their common punctured chart are inverses. -/
theorem simpleCharts_transition (i : G.rootBase.support) {t : K} (ht : t ≠ 0) :
    Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K t) =
      Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K t⁻¹) := by
  apply Variety.mapPoints_injective_of_mono
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
  rw [← Variety.mapPoints_comp, ← Variety.mapPoints_comp,
    simplePositiveChart_points, simpleNegativeChart_points]
  exact congrArg (flagVarietyPointsEquiv G) (simpleRoot_flag_eq_negative G i ht)

private theorem simpleCharts_points_cover (i : G.rootBase.support)
    (q : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    (∃ t : K, Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K t) = q) ∨
      (∃ t : K, Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K t) = q) := by
  have hq : Variety.mapPoints
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q ∈
      Set.range (Variety.mapPoints
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := ⟨q, rfl⟩
  rw [schubertVariety_points_cells] at hq
  obtain ⟨w, hw, p, hp⟩ := Set.mem_iUnion₂.mp hq
  rcases lower_simple G i w hw with rfl | rfl
  · right
    refine ⟨0, ?_⟩
    apply Variety.mapPoints_injective_of_mono
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    rw [← Variety.mapPoints_comp, simpleNegativeChart_points, gaParameterPoint_zero]
    obtain ⟨a, ha⟩ := (Variety.pointsHomeomorph (initialCellIso G)).surjective p
    change Variety.mapPoints (initialCellIso G).hom a = p at ha
    have hi := initialCellIso_points G a
    rw [Variety.mapPoints_comp, ha] at hi
    exact hi.symm.trans hp
  · left
    obtain ⟨a, ha⟩ := (Variety.pointsHomeomorph (simpleCellIso G i)).surjective p
    obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
    change Variety.mapPoints (simpleCellIso G i).hom (additivePointsEquiv K t) = p at ha
    refine ⟨t, ?_⟩
    apply Variety.mapPoints_injective_of_mono
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    rw [simplePositiveChart, Variety.mapPoints_comp, ha,
      ← Variety.mapPoints_comp, schubertCellOfLE_comp]
    exact hp

/-- The two additive open charts cover all scheme points of the simple Schubert variety. -/
theorem simpleCharts_cover (i : G.rootBase.support) :
    Set.range (simplePositiveChart G i).left ∪
      Set.range (simpleNegativeChart G i).left = Set.univ := by
  let X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  have : JacobsonSpace (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver.left :=
    LocallyOfFiniteType.jacobsonSpace X.toSpec
  apply constructible_eq
    ((Variety.isConstructible_range (simplePositiveChart G i)).union
      (Variety.isConstructible_range (simpleNegativeChart G i))) .univ
  ext p
  constructor
  · rintro ⟨_, hp⟩
    exact ⟨Set.mem_univ p, hp⟩
  · rintro ⟨_, hp⟩
    have hp' : p ∈ Set.range X.pointMap := by
      rw [Variety.pointMap_range]
      exact hp
    obtain ⟨q, rfl⟩ := hp'
    rcases simpleCharts_points_cover G i q with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨Or.inl ⟨(additiveVariety K).pointMap (additivePointsEquiv K t), ?_⟩, hp⟩
      rw [← Variety.pointMap_mapPoints, ht]
    · refine ⟨Or.inr ⟨(additiveVariety K).pointMap (additivePointsEquiv K t), ?_⟩, hp⟩
      rw [← Variety.pointMap_mapPoints, ht]
end SchubertGeometry
