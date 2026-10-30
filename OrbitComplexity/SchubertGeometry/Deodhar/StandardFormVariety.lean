import OrbitComplexity.SchubertGeometry.Deodhar.ComponentIsomorphisms
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentRichardson
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterProduct
import OrbitComplexity.SchubertGeometry.Deodhar.StandardForms
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-! # Standard-form subvarieties in the group

The ordered-product lift is a locally closed immersion. Its reduced image inside the group
is the standard-form variety, and the group quotient identifies it with its component.
-/

open CategoryTheory AlgebraicGeometry Topology BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private theorem iso_comp_immersion {S : Scheme} {A B D : Over S}
    (e : A ≅ B) (i : B ⟶ D) [IsImmersion i.left] :
    IsImmersion (e.hom ≫ i).left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  change IsImmersion (e.hom.left ≫ i.left)
  infer_instance

private theorem point_mem_image {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Variety K} (f : A.toOver ⟶ B.toOver) (x : B.points) :
    B.pointMap x ∈ Set.range f.left ↔ x ∈ Set.range (mapPoints f) := by
  constructor
  · exact Variety.exists_mapPoints_eq f x
  · rintro ⟨y, rfl⟩
    exact ⟨A.pointMap y, (Variety.pointMap_mapPoints f y).symm⟩

private theorem image_points_equal {K : Type u} [Field K] [IsAlgClosed K]
    {A B C : Variety K} (f : A.toOver ⟶ C.toOver) (g : B.toOver ⟶ C.toOver)
    (h : Set.range f.left = Set.range g.left) :
    Set.range (mapPoints f) = Set.range (mapPoints g) := by
  ext x
  rw [← point_mem_image f, ← point_mem_image g, h]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)

private instance locallyClosedImmersion (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) : IsImmersion (X.locallyClosedInclusion S hS).left where
  isLocallyClosed_range := by rw [Variety.locallyClosedInclusion_range]; exact hS

private instance cellImmersion (w : G.weylGroup) :
    IsImmersion (schubertCellInclusion G w).left where
  isLocallyClosed_range := by
    rw [GroupActions.orbitInclusion_range]
    exact orbitImage_locallyClosed _ _ _

private theorem componentImmersion : IsImmersion (deodharInclusion G expression hred).left :=
  inferInstanceAs (IsImmersion
    ((deodharPrefixInclusion G expression hred word.length).left ≫
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))).left))

include hred hd in
private theorem liftImmersion :
    IsImmersion (deodharPrefixLift G expression word.length).left := by
  have := componentImmersion G expression hred
  have hc := iso_comp_immersion (deodharComponentIso G expression hred hd)
    (deodharInclusion G expression hred)
  rw [deodharComponentIso_flag] at hc
  have hq : (deodharPrefixLift G expression word.length).left ≫
      (flagQuotientMorphism G).left = (deodharPrefixMorphism G expression word.length).left :=
    congrArg (fun f : (deodharParameters G expression).toOver ⟶ (flagVariety G).toOver =>
      f.left) (deodharPrefixLift_projection G expression word.length)
  have : IsImmersion ((deodharPrefixLift G expression word.length).left ≫
      (flagQuotientMorphism G).left) := by rw [hq]; exact hc
  exact IsImmersion.of_comp _ (flagQuotientMorphism G).left

include hred hd in
private theorem liftLocallyClosed :
    IsLocallyClosed (Set.range (deodharPrefixLift G expression word.length).left) := by
  have := liftImmersion G expression hred hd
  exact (deodharPrefixLift G expression word.length).left.isLocallyClosed_range

/-- The standard-form variety is the reduced locally closed product image inside the group. -/
def deodharStandardVariety : Variety K :=
  (reductiveVariety G).locallyClosedSubvariety
    (Set.range (deodharPrefixLift G expression word.length).left)
    (liftLocallyClosed G expression hred hd)

/-- The standard-form variety includes into the ambient reductive group. -/
def deodharStandardInclusion :
    (deodharStandardVariety G expression hred hd).toOver ⟶ (reductiveVariety G).toOver :=
  (reductiveVariety G).locallyClosedInclusion
    (Set.range (deodharPrefixLift G expression word.length).left)
    (liftLocallyClosed G expression hred hd)

private theorem standard_range :
    Set.range (deodharStandardInclusion G expression hred hd).left =
      Set.range (deodharPrefixLift G expression word.length).left :=
  Variety.locallyClosedInclusion_range _ _ _

private instance standard_preimmersion :
    IsPreimmersion (deodharStandardInclusion G expression hred hd).left := by
  exact Variety.locallyClosedInclusion_isPreimmersion (reductiveVariety G) _ _

private theorem standard_points_range :
    Set.range (mapPoints (deodharPrefixLift G expression word.length)) =
      Set.range (mapPoints (deodharStandardInclusion G expression hred hd)) :=
  image_points_equal _ _ (standard_range G expression hred hd).symm

/-- Ordered product parameters identify with their reduced locally closed group image. -/
def deodharStandardParamIso : (deodharParameters G expression).toOver ≅
    (deodharStandardVariety G expression hred hd).toOver := by
  have := liftImmersion G expression hred hd
  exact Variety.pointImageIso (deodharPrefixLift G expression word.length)
    (deodharStandardInclusion G expression hred hd)
    (standard_points_range G expression hred hd)

/-- The parameter chart of the standard-form variety is its ordered group product. -/
@[reassoc]
theorem deodharStandardParamIso_lift :
    (deodharStandardParamIso G expression hred hd).hom ≫
      deodharStandardInclusion G expression hred hd =
        deodharPrefixLift G expression word.length := by
  have := liftImmersion G expression hred hd
  exact Variety.pointImageIso_hom_comp _ _ (standard_points_range G expression hred hd)

/-- The standard-form variety maps isomorphically to its intrinsic flag component. -/
def deodharStandardComponentIso :
    (deodharStandardVariety G expression hred hd).toOver ≅
      (deodharComponent G expression hred).toOver :=
  (deodharStandardParamIso G expression hred hd).symm ≪≫
    deodharComponentIso G expression hred hd

/-- The standard-form isomorphism is induced by the quotient morphism to flags. -/
@[reassoc]
theorem deodharStandardComponentIso_quotient :
    (deodharStandardComponentIso G expression hred hd).hom ≫
      deodharInclusion G expression hred =
        deodharStandardInclusion G expression hred hd ≫ flagQuotientMorphism G := by
  apply (cancel_epi (deodharStandardParamIso G expression hred hd).hom).mp
  simp only [deodharStandardComponentIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, Iso.hom_inv_id_assoc, deodharComponentIso_flag,
    ← Category.assoc, deodharStandardParamIso_lift, deodharPrefixLift_projection]

/-- Standard forms are a split torus in omitted positions times affine decreasing coordinates. -/
def deodharStandardProductIso :
    (deodharStandardVariety G expression hred hd).toOver ≅
      (reductiveVariety (SplitTorus.groupData K
        (deodharEqualPositions G expression))).toOver ⊗
          (affineSpaceVariety K {j : deodharIndex G expression //
            j ∉ deodharEqualPositions G expression}).toOver :=
  (deodharStandardParamIso G expression hred hd).symm ≪≫
    deodharParameterProductIso G expression

/-- The group points of the standard-form variety are exactly the admissible ordered products. -/
theorem deodharStandard_points :
    Set.range (fun x : (deodharStandardVariety G expression hred hd).points =>
      (reductivePointsEquiv G).symm
        (mapPoints (deodharStandardInclusion G expression hred hd) x)) =
      {g | ∃ p : Fin word.length → K,
        (∀ j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression, p j ≠ 0) ∧
          deodharPrefix G expression p word.length = g} := by
  have h := standard_points_range G expression hred hd
  have hi := congrArg (fun S => (reductivePointsEquiv G).symm '' S) h
  simp only [← Set.range_comp, Function.comp_def] at hi
  exact hi.symm.trans (deodharPrefixLift_image G expression word.length)

end
end SchubertGeometry

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety
namespace SchubertGeometry
noncomputable section
universe u

private theorem inverse_quotient {C : Type*} [Category C] {A B H F : C}
    (e : A ≅ B) (a : A ⟶ H) (b : B ⟶ F) (q : H ⟶ F)
    (h : e.hom ≫ b = a ≫ q) : e.inv ≫ a ≫ q = b := by
  rw [← h, e.inv_hom_id_assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)

/-- The inverse standard-form chart is a regular representative map into the group. -/
def deodharStandardFormMap :
    (deodharComponent G expression hred).toOver ⟶ (reductiveVariety G).toOver :=
  (deodharStandardComponentIso G expression hred hd).inv ≫
    deodharStandardInclusion G expression hred hd

private theorem standardForm_parameters :
    deodharStandardFormMap G expression hred hd =
      (deodharComponentIso G expression hred hd).inv ≫
        deodharPrefixLift G expression word.length := by
  change ((deodharStandardParamIso G expression hred hd).symm ≪≫
    deodharComponentIso G expression hred hd).inv ≫ _ = _
  rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, deodharStandardParamIso_lift]

/-- The regular standard representative projects to the original component flag. -/
@[reassoc]
theorem deodharStandardFormMap_quotient :
    deodharStandardFormMap G expression hred hd ≫ flagQuotientMorphism G =
      deodharInclusion G expression hred := by
  exact inverse_quotient (deodharStandardComponentIso G expression hred hd)
    (deodharStandardInclusion G expression hred hd) (deodharInclusion G expression hred)
    (flagQuotientMorphism G) (deodharStandardComponentIso_quotient G expression hred hd)

/-- Standard representatives factor into the ordered selected root maps
and signed representative. -/
theorem deodharStandardFormMap_rootProduct
    (x : (deodharComponent G expression hred).points) :
    mapPoints (deodharStandardFormMap G expression hred hd) x =
      reductivePointsEquiv G (subwordRootProduct G expression
        (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
          (mapPoints (deodharParameterInclusion G expression)
            (mapPoints (deodharComponentIso G expression hred hd).inv x)) ⟨j⟩)
        word.length * subwordRepresentative G expression word.length) := by
  have h := congrArg (fun f : (deodharComponent G expression hred).toOver ⟶
    (reductiveVariety G).toOver => mapPoints (X := deodharComponent G expression hred)
      (Y := reductiveVariety G) f x) (standardForm_parameters G expression hred hd)
  exact h.trans ((mapPoints_comp
    (X := deodharComponent G expression hred) (Y := deodharParameters G expression)
    (Z := reductiveVariety G) (deodharComponentIso G expression hred hd).inv
    (deodharPrefixLift G expression word.length) x).trans
      (deodharPrefixLift_points G expression word.length
        (mapPoints (deodharComponentIso G expression hred hd).inv x)))

end
end SchubertGeometry

open scoped Pointwise
namespace SchubertGeometry
noncomputable section
universe u

private theorem ordered_image_prod {ι A M : Type*} [Monoid M] [Nonempty A]
    (l : List ι) (hl : l.Nodup) (f : ι → A → M) (S : ι → Set A) :
    (l.map (fun i => f i '' S i)).prod =
      {g | ∃ p : ι → A, (∀ i ∈ l, p i ∈ S i) ∧
        (l.map (fun i => f i (p i))).prod = g} := by
  classical
  revert hl
  induction l with
  | nil =>
    intro _
    ext g
    simp only [List.map_nil, List.prod_nil, Set.mem_one, Set.mem_ofPred_eq]
    constructor
    · intro hg
      exact ⟨fun _ => Classical.arbitrary A, by simp, hg.symm⟩
    · rintro ⟨_, _, hg⟩
      exact hg.symm
  | cons i l ih =>
    intro hl
    obtain ⟨hi, htail⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons, ih htail]
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hg
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨p, hp, hprod⟩ := hy
      refine ⟨Function.update p i a, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · simpa only [Function.update_self] using ha
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
          exact hp j hj
      · have hmap : l.map (fun j => f j (Function.update p i a j)) =
            l.map (fun j => f j (p j)) := by
          apply List.map_congr_left
          intro j hj
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
        simpa only [List.map_cons, List.prod_cons, Function.update_self, hmap, hprod] using hxy
    · rintro ⟨p, hp, hprod⟩
      refine Set.mem_mul.mpr ⟨f i (p i), ⟨p i, hp i (by simp), rfl⟩,
        (l.map (fun j => f j (p j))).prod, ?_, ?_⟩
      · exact ⟨p, fun j hj => hp j (List.mem_cons_of_mem i hj), rfl⟩
      · simpa only [List.map_cons, List.prod_cons] using hprod


variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def selectedChoice (j : Fin word.length) : Option
    {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression} := by
  classical
  exact if h : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression then some ⟨j, h⟩ else none

private def selectedOrder := (List.finRange word.length).filterMap (selectedChoice G expression)

private theorem selectedChoice_val (a : Fin word.length)
    (b : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression})
    (h : b ∈ selectedChoice G expression a) : b.val = a := by
  classical
  unfold selectedChoice at h
  split at h
  · exact (congrArg Subtype.val (Option.mem_some_iff.mp h)).symm
  · exact False.elim (Option.not_mem_none _ h)

private theorem selectedOrder_nodup : (selectedOrder G expression).Nodup :=
  List.Nodup.filterMap
    (fun a b j ha hb => (selectedChoice_val G expression a j ha).symm.trans
      (selectedChoice_val G expression b j hb)) (List.nodup_finRange word.length)

private theorem selectedOrder_mem
    (j : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression}) :
    j ∈ selectedOrder G expression := by
  classical
  exact List.mem_filterMap.mpr ⟨j.val, List.mem_finRange j.val,
    by simp only [selectedChoice, j.property, ↓reduceDIte]⟩

private theorem rootProduct_expansion
    (p : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression} → K) :
    subwordRootProduct G expression p word.length =
      ((selectedOrder G expression).map
        (fun j => gaParameterPoint (subwordRootMap G expression j) (p j))).prod := by
  unfold subwordRootProduct
  rw [List.take_of_length_le (by simp only [List.length_finRange, le_refl])]
  rfl

/-- A selected root factor is punctured at an omitted position and unrestricted at a decrease. -/
def deodharRootFactorSet
    (j : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression}) : Set G.points :=
  (fun a : K => gaParameterPoint (subwordRootMap G expression j) a) ''
    {a | j.val ∈ equalSteps (weylCoxeterSystem G.rootBase) expression → a ≠ 0}

/-- The selected root-factor sets are multiplied in their original word order. -/
def deodharRootProductSet : Set G.points :=
  ((selectedOrder G expression).map (deodharRootFactorSet G expression)).prod

private theorem rootProductSet_parameters :
    deodharRootProductSet G expression =
      {g | ∃ p : {j : Fin word.length //
          j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
            negativeSteps (weylCoxeterSystem G.rootBase) expression} → K,
        (∀ j, j.val ∈ equalSteps (weylCoxeterSystem G.rootBase) expression → p j ≠ 0) ∧
          subwordRootProduct G expression p word.length = g} := by
  unfold deodharRootProductSet deodharRootFactorSet
  rw [ordered_image_prod _ (selectedOrder_nodup G expression)]
  ext g
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, fun j hj => hp j (selectedOrder_mem G expression j) hj,
      (rootProduct_expansion G expression p).trans he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, fun j _ => hp j, (rootProduct_expansion G expression p).symm.trans he⟩

/-- Standard forms are the ordered selected root-factor sets times their signed representative. -/
theorem deodharStandard_products
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    Set.range (fun x : (deodharStandardVariety G expression hred hd).points =>
      (reductivePointsEquiv G).symm
        (mapPoints (deodharStandardInclusion G expression hred hd) x)) =
      deodharRootProductSet G expression * {subwordRepresentative G expression word.length} := by
  rw [deodharStandard_points G expression hred hd]
  ext g
  constructor
  · rintro ⟨p, hp, he⟩
    refine Set.mem_mul.mpr ⟨subwordRootProduct G expression (fun j => p j.val)
      word.length, ?_, subwordRepresentative G expression word.length, rfl, ?_⟩
    · rw [rootProductSet_parameters G expression]
      exact ⟨fun j => p j.val, fun j hj => hp j.val hj, rfl⟩
    · exact (deodharPrefix_rootProduct G expression p word.length).symm.trans he
  · intro hg
    obtain ⟨a, ha, b, hb, he⟩ := Set.mem_mul.mp hg
    obtain ⟨p, hp, hpa⟩ := (rootProductSet_parameters G expression).subset ha
    have hb' : b = subwordRepresentative G expression word.length := hb
    subst b
    let q := Function.extend Subtype.val p (fun _ : Fin word.length => (0 : K))
    have hq (j : {j : Fin word.length //
        j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
          negativeSteps (weylCoxeterSystem G.rootBase) expression}) : q j.val = p j :=
      Function.Injective.extend_apply Subtype.val_injective _ _ j
    have hc : (fun j => q j.val) = p := funext hq
    refine ⟨q, ?_, ?_⟩
    · intro j hj
      rw [hq ⟨j, Or.inl hj⟩]
      exact hp ⟨j, Or.inl hj⟩ hj
    · rw [deodharPrefix_rootProduct G expression q word.length, hc, hpa]
      exact he

end
end SchubertGeometry
