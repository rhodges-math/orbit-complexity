import OrbitComplexity.GroupActions.Varieties.RootProductPoints
import OrbitComplexity.GroupActions.Varieties.UnipotentPoints
import OrbitComplexity.GroupActions.Varieties.OppositeUnipotentPoints
import OrbitComplexity.GroupActions.Varieties.ReductiveConjugation
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootClosedSets
import Batteries.Tactic.Lint

/-!
# Root-product coordinates on the opposite unipotent group

The simple noninversion roots and the simple inversion root split the positive
unipotent group as a product of varieties. Conjugation by the longest Weyl
representative gives the corresponding coordinates on the opposite group.
-/

open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups Topology

namespace SchubertGeometry.DeterminantSection

noncomputable section

universe u

private theorem subgroup_image_range {K : Type u} [Field K]
    {X Y Z : Variety K} {M : Type u} [Group M] {H J : Subgroup M}
    (e : M ≃ Z.points) (a : M ≃ M) (eX : X.points ≃ H) (eY : Y.points ≃ J)
    (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    (hf : ∀ x, Variety.mapPoints f x = e (a (eX x)))
    (hg : ∀ y, Variety.mapPoints g y = e (eY y))
    (ha : ∀ p, a p ∈ J ↔ p ∈ H) :
    Set.range (Variety.mapPoints f) = Set.range (Variety.mapPoints g) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    let q : J := ⟨a (eX x), (ha _).mpr (eX x).property⟩
    refine ⟨eY.symm q, ?_⟩
    rw [hg, eY.apply_symm_apply]
    exact (hf x).symm
  · rintro ⟨y, rfl⟩
    have hq : a.symm (eY y) ∈ H := (ha _).mp (by
      simpa only [a.apply_symm_apply] using (eY y).property)
    let q : H := ⟨a.symm (eY y), hq⟩
    refine ⟨eX.symm q, ?_⟩
    rw [hf, eX.apply_symm_apply]
    change e (a (a.symm (eY y))) = Variety.mapPoints g y
    rw [a.apply_symm_apply]
    exact (hg y).symm

private theorem iso_triple_comp {C : Type*} [Category C]
    {X Y Z W A : C} (e : X ≅ Y) (d : Y ≅ Z) (q : Z ≅ W)
    (iY : Y ⟶ A) (iZ : Z ⟶ A) (iW : W ⟶ A) (c : A ⟶ A)
    (hd : d.hom ≫ iZ = iY) (hq : q.hom ≫ iW = iZ ≫ c) :
    (e ≪≫ d ≪≫ q).hom ≫ iW = (e.hom ≫ iY) ≫ c := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [hq, ← Category.assoc d.hom iZ c, hd]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

private theorem all_root_points :
    G.rootSubsetPoints {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) = G.unipotentPoints := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    exact G.rootSubsetPoints_le_unipotent {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) hg
  · intro hg
    rw [G.rootSubsetPoints_eq]
    apply Subgroup.mem_map.mpr
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    change ∀ c, c ∉ G.rootCharacters {r | G.rootBase.IsPos r} → _
    intro c hc
    apply (hc ?_).elim
    change G.rootBase.IsPos
      (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit c))
    exact (G.borelCharacterRootEquiv c).property

private theorem all_root_range :
    Set.range (Variety.mapPoints (rootSubsetInclusion G {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase))) =
      Set.range (Variety.mapPoints (unipotentInclusion G)) := by
  apply subgroup_image_range (reductivePointsEquiv G) (Equiv.refl G.points)
    (rootSubsetPointsMulEquiv G _ _).toEquiv (unipotentPointsMulEquiv G).toEquiv
  · exact rootSubsetInclusion_points G _ _
  · exact unipotentInclusion_points G
  · intro p
    change p ∈ G.unipotentPoints ↔
      p ∈ G.rootSubsetPoints {r | G.rootBase.IsPos r}
        (isPositiveRootClosed_isPos G.rootBase)
    rw [all_root_points G]

private def allRootIso :
    (rootSubsetVariety G {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase)).toOver ≅ (unipotentVariety G).toOver :=
  Variety.pointImageIso
    (rootSubsetInclusion G {r | G.rootBase.IsPos r} (isPositiveRootClosed_isPos G.rootBase))
    (unipotentInclusion G) (all_root_range G)

private theorem allRootIso_comp :
    (allRootIso G).hom ≫ unipotentInclusion G =
      rootSubsetInclusion G {r | G.rootBase.IsPos r}
        (isPositiveRootClosed_isPos G.rootBase) :=
  Variety.pointImageIso_hom_comp _ _ (all_root_range G)

private def unipotentConjugateMap :
    (unipotentVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  unipotentInclusion G ≫ (reductiveConjugation G G.longestPoint).hom

private instance unipotentConjugateMap_preimmersion :
    IsPreimmersion (unipotentConjugateMap G).left := by
  change IsPreimmersion ((unipotentInclusion G).left ≫
    (reductiveConjugation G G.longestPoint).hom.left)
  infer_instance

private theorem conjugate_unipotent_range :
    Set.range (Variety.mapPoints (unipotentConjugateMap G)) =
      Set.range (Variety.mapPoints (oppositeUnipotentInclusion G)) := by
  apply subgroup_image_range (reductivePointsEquiv G)
    (MulAut.conj G.longestPoint).toEquiv (unipotentPointsMulEquiv G).toEquiv
    (oppositeUnipotentPointsMulEquiv G).toEquiv
  · intro x
    change Variety.mapPoints
      (unipotentInclusion G ≫ (reductiveConjugation G G.longestPoint).hom) x = _
    rw [Variety.mapPoints_comp, unipotentInclusion_points, reductiveConjugation_points]
    rfl
  · exact oppositeUnipotentInclusion_points G
  · exact G.conj_mem_oppositeUnipotent

private def unipotentOppositeIso :
    (unipotentVariety G).toOver ≅ (oppositeUnipotentVariety G).toOver :=
  Variety.pointImageIso (unipotentConjugateMap G) (oppositeUnipotentInclusion G)
    (conjugate_unipotent_range G)

private theorem unipotentOppositeIso_comp :
    (unipotentOppositeIso G).hom ≫ oppositeUnipotentInclusion G =
      unipotentInclusion G ≫ (reductiveConjugation G G.longestPoint).hom :=
  Variety.pointImageIso_hom_comp _ _ (conjugate_unipotent_range G)

private def simpleElement (i : G.rootBase.support) : G.weylGroup :=
  RootPairing.weylGroup.ofIdx G.rootSystem i

private def simpleNoninversions (i : G.rootBase.support) : Set G.rootIndex :=
  {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase (simpleElement G i)}

private def simpleInversions (i : G.rootBase.support) : Set G.rootIndex :=
  leftRootInversionIndices G.rootBase (simpleElement G i)

private theorem simple_noninversions_closed (i : G.rootBase.support) :
    IsPositiveRootClosed G.rootBase (simpleNoninversions G i) :=
  PositiveRootClosedSets.isPositiveRootClosed G.rootBase (simpleElement G i)

private theorem simple_inversions_closed (i : G.rootBase.support) :
    IsPositiveRootClosed G.rootBase (simpleInversions G i) :=
  LeftRootInversionIndices.isPositiveRootClosed G.rootBase (simpleElement G i)

private theorem simple_root_partition (i : G.rootBase.support) :
    {r | G.rootBase.IsPos r} = simpleNoninversions G i ∪ simpleInversions G i := by
  ext r
  change G.rootBase.IsPos r ↔
    (G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase (simpleElement G i)) ∨
      r ∈ leftRootInversionIndices G.rootBase (simpleElement G i)
  constructor
  · intro hr
    by_cases hi : r ∈ leftRootInversionIndices G.rootBase (simpleElement G i)
    · exact Or.inr hi
    · exact Or.inl ⟨hr, hi⟩
  · rintro (hr | hr)
    · exact hr.1
    · exact ((mem_leftRootInversionIndices G.rootBase (simpleElement G i) r).mp hr).1

private theorem simple_root_disjoint (i : G.rootBase.support) :
    Disjoint (simpleNoninversions G i) (simpleInversions G i) :=
  Set.disjoint_left.mpr (fun _ hr hi => hr.2 hi)

/-- The root-product variety providing coordinates on the opposite unipotent group,
with one factor corresponding to a simple root. -/
def oppositeRootProduct (i : G.rootBase.support) : Variety K :=
  rootProductVariety G (simpleNoninversions G i) (simpleInversions G i)
    (simple_noninversions_closed G i) (simple_inversions_closed G i)

private def positiveProductIso (i : G.rootBase.support) :
    (oppositeRootProduct G i).toOver ≅
      (rootSubsetVariety G {r | G.rootBase.IsPos r}
        (isPositiveRootClosed_isPos G.rootBase)).toOver :=
  rootProductIso G _ _ _ (isPositiveRootClosed_isPos G.rootBase)
    (simple_noninversions_closed G i) (simple_inversions_closed G i)
    (simple_root_partition G i) (simple_root_disjoint G i)

/-- Conjugated multiplication of the simple root-product factors into the group. -/
def oppositeRootProductMap (i : G.rootBase.support) :
    (oppositeRootProduct G i).toOver ⟶ (reductiveVariety G).toOver :=
  ((positiveProductIso G i).hom ≫ rootSubsetInclusion G {r | G.rootBase.IsPos r}
    (isPositiveRootClosed_isPos G.rootBase)) ≫
      (reductiveConjugation G G.longestPoint).hom

/-- The simple root-product chart is an isomorphism onto the opposite unipotent group. -/
def oppositeRootProductIso (i : G.rootBase.support) :
    (oppositeRootProduct G i).toOver ≅ (oppositeUnipotentVariety G).toOver :=
  positiveProductIso G i ≪≫ allRootIso G ≪≫ unipotentOppositeIso G

/-- The root-product isomorphism agrees with conjugated group multiplication. -/
theorem oppositeRootProductIso_comp (i : G.rootBase.support) :
    (oppositeRootProductIso G i).hom ≫ oppositeUnipotentInclusion G =
      oppositeRootProductMap G i :=
  iso_triple_comp (positiveProductIso G i) (allRootIso G) (unipotentOppositeIso G)
    (rootSubsetInclusion G {r | G.rootBase.IsPos r} (isPositiveRootClosed_isPos G.rootBase))
    (unipotentInclusion G) (oppositeUnipotentInclusion G)
    (reductiveConjugation G G.longestPoint).hom
    (allRootIso_comp G) (unipotentOppositeIso_comp G)

end

end SchubertGeometry.DeterminantSection
