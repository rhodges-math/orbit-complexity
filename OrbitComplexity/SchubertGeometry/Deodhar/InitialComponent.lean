import OrbitComplexity.SchubertGeometry.Deodhar.Components
import OrbitComplexity.SchubertGeometry.Deodhar.InitialCell
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterInitial
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterMaps

/-! # The initial intrinsic Deodhar component

The empty ordinary cell is the base spectrum, and its flag satisfies the initial
opposite-cell condition. The reduced intrinsic component is therefore the same spectrum.
Composing with the empty-parameter isomorphism gives the initial parametrization.
-/

open CategoryTheory AlgebraicGeometry Topology BruhatIntervals ReductiveGroups SchubertGeometry
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem initial_opposite : flagVarietyPointsEquiv G (flagProjection G 1) ∈
    Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G 1)) := by
  rw [oppositeSchubertCell_points_range]
  have h : weylFlagPoint G 1 = flagVarietyPointsEquiv G (flagProjection G 1) := by
    rw [weylFlagPoint, G.weylPoint_eq, weylElementPoint_one]
  rw [← h]
  exact MulAction.mem_orbit_self _

private theorem family_transport {I C : Type*} [Category C] (F : I → C) {Z A : C}
    (f : ∀ i, F i ⟶ Z) {i j : I} (h : i = j) (e : A ≅ F j) :
    (e ≪≫ eqToIso (congrArg F h.symm)).hom ≫ f i = e.hom ≫ f j := by
  subst i
  simp only [eqToIso_refl, Iso.trans_refl]

private theorem initial_word : simpleWeylWord G.rootBase (word.take 0) = 1 := by
  simp only [List.take_zero, simpleWeylWord]

private def initial_word_iso :
    (GroupActions.affineVariety K K).toOver ≅ (wordCell G word 0).toOver :=
  initialCellIso G ≪≫ eqToIso (congrArg
    (fun w : G.weylGroup => (schubertCell G w).toOver) (initial_word G (word := word)).symm)

private theorem initial_word_points (p : (GroupActions.affineVariety K K).points) :
    GroupActions.Variety.mapPoints ((initial_word_iso G (word := word)).hom ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take 0))) p =
        flagVarietyPointsEquiv G (flagProjection G 1) := by
  have hf := family_transport (fun w : G.weylGroup => (schubertCell G w).toOver)
    (fun w => schubertCellInclusion G w) (initial_word G (word := word)) (initialCellIso G)
  exact (congrArg (fun f : (GroupActions.affineVariety K K).toOver ⟶
    (flagVariety G).toOver => GroupActions.Variety.mapPoints f p) hf).trans
      (initialCellIso_points G p)

private theorem initial_image :
    Set.range (GroupActions.Variety.mapPoints (initial_word_iso G (word := word)).hom) =
      Set.range (GroupActions.Variety.mapPoints (deodharPrefixInclusion G expression hred 0)) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    apply (mem_deodharPrefix_points G expression hred 0 _).mpr
    intro k
    have hk : k = 0 := Fin.ext (by have := k.isLt; omega)
    subst k
    let j := schubertCellInclusion G (simpleWeylWord G.rootBase (word.take 0))
    have hf : wordCellProjection G word hred (Nat.le_refl 0) ≫ j = j :=
      (congrArg (fun g : (wordCell G word 0).toOver ⟶ (wordCell G word 0).toOver =>
        g ≫ j) (wordCellProjection_self G word hred 0)).trans (Category.id_comp j)
    change GroupActions.Variety.mapPoints
      (wordCellProjection G word hred (Nat.le_refl 0) ≫ j)
      (GroupActions.Variety.mapPoints (initial_word_iso G (word := word)).hom p) ∈
        Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G 1))
    have hp : GroupActions.Variety.mapPoints j
        (GroupActions.Variety.mapPoints (initial_word_iso G (word := word)).hom p) =
          flagVarietyPointsEquiv G (flagProjection G 1) :=
      (GroupActions.Variety.mapPoints_comp _ _ p).symm.trans (initial_word_points G p)
    exact (congrArg (fun f : (wordCell G word 0).toOver ⟶ (flagVariety G).toOver =>
      GroupActions.Variety.mapPoints f
        (GroupActions.Variety.mapPoints (initial_word_iso G (word := word)).hom p)) hf).symm ▸
      (hp.symm ▸ initial_opposite G)
  · intro _
    exact (GroupActions.Variety.pointsHomeomorph
      (initial_word_iso G (word := word))).surjective x

omit [IsAlgClosed K] [CharZero K] in
private theorem iso_pre {A B : Over (Spec (CommRingCat.of K))} (e : A ≅ B) :
    IsPreimmersion e.hom.left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  infer_instance

private instance initial_prefix_pre :
    IsPreimmersion (deodharPrefixInclusion G expression hred 0).left := by
  dsimp only [deodharPrefixInclusion]
  infer_instance

private def imageData {X Y Z : GroupActions.Variety K}
    (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    [IsPreimmersion f.left] [IsPreimmersion g.left]
    (hp : Set.range (GroupActions.Variety.mapPoints f) =
      Set.range (GroupActions.Variety.mapPoints g)) :
    {e : X.toOver ≅ Y.toOver // e.hom ≫ g = f} :=
  ⟨GroupActions.Variety.pointImageIso f g hp,
    GroupActions.Variety.pointImageIso_hom_comp f g hp⟩

private def initial_data :
    {e : (GroupActions.affineVariety K K).toOver ≅
      (deodharPrefixComponent G expression hred 0).toOver //
      e.hom ≫ deodharPrefixInclusion G expression hred 0 =
        (initial_word_iso G (word := word)).hom} := by
  letI : IsPreimmersion (initial_word_iso G (word := word)).hom.left :=
    iso_pre (initial_word_iso G (word := word))
  letI : IsPreimmersion (deodharPrefixInclusion G expression hred 0).left :=
    initial_prefix_pre G expression hred
  exact imageData
    (X := GroupActions.affineVariety K K)
    (Y := deodharPrefixComponent G expression hred 0) (Z := wordCell G word 0)
    (initial_word_iso G (word := word)).hom
    (deodharPrefixInclusion G expression hred 0) (initial_image G expression hred)

/-- The empty-prefix intrinsic component is the spectrum of the base field. -/
@[irreducible] def initialComponentIso : (GroupActions.affineVariety K K).toOver ≅
    (deodharPrefixComponent G expression hred 0).toOver :=
  (initial_data G expression hred).val

private theorem initialComponentIso_projection :
    (initialComponentIso G expression hred).hom ≫
      deodharPrefixInclusion G expression hred 0 =
        (initial_word_iso G (word := word)).hom :=
by
  simpa only [initialComponentIso] using (initial_data G expression hred).property

/-- The initial component isomorphism preserves its map to the flag variety. -/
theorem initialComponentIso_flag :
    (initialComponentIso G expression hred).hom ≫
      deodharPrefixInclusion G expression hred 0 ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take 0)) =
          (initialCellIso G).hom ≫ schubertCellInclusion G 1 := by
  have h := initialComponentIso_projection G expression hred
  have hpost := congrArg (fun f : (GroupActions.affineVariety K K).toOver ⟶
      (wordCell G word 0).toOver => f ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take 0))) h
  have ht := family_transport (fun w : G.weylGroup => (schubertCell G w).toOver)
    (fun w => schubertCellInclusion G w) (initial_word G (word := word)) (initialCellIso G)
  exact (Category.assoc _ _ _).symm.trans (hpost.trans ht)

private theorem trans_map {C : Type*} [Category C] {A B D E F : C}
    (d : A ≅ B) (e : B ≅ D) (i : D ⟶ E) (j : E ⟶ F) :
    (d ≪≫ e).hom ≫ i ≫ j = d.hom ≫ (e.hom ≫ i ≫ j) := by
  simp only [Iso.trans_hom, Category.assoc]

/-- Empty-prefix parameters give the initial intrinsic component. -/
@[irreducible] def deodharBaseIso :
    (deodharParameters G (expression.take 0)).toOver ≅
      (deodharPrefixComponent G expression hred 0).toOver :=
  deodharInitialIso G expression ≪≫ initialComponentIso G expression hred

/-- The initial parameter isomorphism has the prescribed regular flag morphism. -/
theorem deodharBaseIso_flag :
    (deodharBaseIso G expression hred).hom ≫
      deodharPrefixInclusion G expression hred 0 ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take 0)) =
          deodharPrefixMorphism G (expression.take 0) 0 := by
  have h := (trans_map (deodharInitialIso G expression)
    (initialComponentIso G expression hred) (deodharPrefixInclusion G expression hred 0)
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take 0)))).trans
      (congrArg (fun f : (GroupActions.affineVariety K K).toOver ⟶
        (flagVariety G).toOver => (deodharInitialIso G expression).hom ≫ f)
          (initialComponentIso_flag G expression hred))
  have hb : (deodharInitialIso G expression).hom ≫
      ((initialCellIso G).hom ≫ schubertCellInclusion G 1) =
        deodharPrefixMorphism G (expression.take 0) 0 := by
    apply GroupActions.Variety.mapPoints_injective
      (X := deodharParameters G (expression.take 0)) (Y := flagVariety G)
    funext x
    have hl := (GroupActions.Variety.mapPoints_comp (deodharInitialIso G expression).hom
      ((initialCellIso G).hom ≫ schubertCellInclusion G 1) x).trans
        (initialCellIso_points G _)
    have hr := deodharPrefixMorphism_points G (expression.take 0) 0 x
    have hp : subwordRootProduct G (expression.take 0)
        (fun j => GroupActions.affineSpaceVarietyPointsEquiv K
          (deodharIndex G (expression.take 0))
          (GroupActions.Variety.mapPoints (deodharParameterInclusion G (expression.take 0)) x)
            ⟨j⟩) 0 * subwordRepresentative G (expression.take 0) 0 = 1 := by
      simp only [subwordRootProduct, subwordRepresentative, List.take_zero, List.prod_nil, mul_one]
      rfl
    exact hl.trans ((congrArg (fun g : G.points =>
      flagVarietyPointsEquiv G (flagProjection G g)) hp).symm.trans hr.symm)
  simpa only [deodharBaseIso] using h.trans hb

end
end SchubertGeometry
