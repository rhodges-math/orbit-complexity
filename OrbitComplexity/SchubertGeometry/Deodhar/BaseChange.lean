import OrbitComplexity.SchubertGeometry.Deodhar.ProductChart

/-! # Base change of increasing cell projections

The product chart pulls back along any scheme morphism to the preceding cell. The
resulting isomorphism preserves the base projection and the extension-chart morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private def chartPullbackIso {D : Type*} [Category D] [CartesianMonoidalCategory D]
    [HasPullbacks D] {B A E X : D} (e : B ⊗ A ≅ E) (π : E ⟶ B)
    (h : e.hom ≫ π = fst B A) (f : X ⟶ B) : X ⊗ A ≅ pullback f π := by
  let c : X ⊗ A ⟶ E := (f ⊗ₘ 𝟙 A) ≫ e.hom
  have hc : c ≫ π = fst X A ≫ f := by
    rw [show c = (f ⊗ₘ 𝟙 A) ≫ e.hom from rfl, Category.assoc, h, tensorHom_fst]
  have hi : e.inv ≫ fst B A = π := by
    rw [← h, e.inv_hom_id_assoc]
  refine
    { hom := pullback.lift (fst X A) c hc.symm
      inv := lift (pullback.fst f π) (pullback.snd f π ≫ e.inv ≫ snd B A)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [comp_lift, pullback.lift_fst, lift_fst, Category.id_comp]
    · simp only [comp_lift, pullback.lift_snd_assoc, lift_snd]
      dsimp only [c]
      rw [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_snd,
        Category.comp_id, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, lift_fst, Category.id_comp]
    · apply (cancel_mono e.inv).mp
      simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      dsimp only [c]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, hi]
        exact pullback.condition
      · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]

private theorem chartPullbackIso_fst {D : Type*} [Category D] [CartesianMonoidalCategory D]
    [HasPullbacks D] {B A E X : D} (e : B ⊗ A ≅ E) (π : E ⟶ B)
    (h : e.hom ≫ π = fst B A) (f : X ⟶ B) :
    (chartPullbackIso e π h f).hom ≫ pullback.fst f π = fst X A :=
  pullback.lift_fst _ _ _

private theorem chartPullbackIso_snd {D : Type*} [Category D] [CartesianMonoidalCategory D]
    [HasPullbacks D] {B A E X : D} (e : B ⊗ A ≅ E) (π : E ⟶ B)
    (h : e.hom ≫ π = fst B A) (f : X ⟶ B) :
    (chartPullbackIso e π h f).hom ≫ pullback.snd f π = (f ⊗ₘ 𝟙 A) ≫ e.hom :=
  pullback.lift_snd _ _ _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
  (X : Over (Spec (CommRingCat.of K))) (f : X ⟶ (schubertCell G w).toOver)

/-- Any base change of the increasing-cell projection is the product with Ga. -/
def rankOneCellPullbackIso : X ⊗ (GroupActions.additiveVariety K).toOver ≅
    pullback f (rankOneCellProjection G w i hw) :=
  chartPullbackIso (rankOneCellProductIso G w i hw) (rankOneCellProjection G w i hw)
    (rankOneCellProductIso_projection G w i hw) f

/-- The cell pullback isomorphism preserves the projection to its base. -/
theorem rankOneCellPullbackIso_fst : (rankOneCellPullbackIso G w i hw X f).hom ≫
    pullback.fst f (rankOneCellProjection G w i hw) =
      fst X (GroupActions.additiveVariety K).toOver :=
  chartPullbackIso_fst (rankOneCellProductIso G w i hw) (rankOneCellProjection G w i hw)
    (rankOneCellProductIso_projection G w i hw) f

/-- The map from the pullback to the extended cell is the base-changed product chart. -/
theorem rankOneCellPullbackIso_snd : (rankOneCellPullbackIso G w i hw X f).hom ≫
    pullback.snd f (rankOneCellProjection G w i hw) =
      (f ⊗ₘ 𝟙 (GroupActions.additiveVariety K).toOver) ≫
        (rankOneCellProductIso G w i hw).hom :=
  chartPullbackIso_snd (rankOneCellProductIso G w i hw) (rankOneCellProjection G w i hw)
    (rankOneCellProductIso_projection G w i hw) f

end
end SchubertGeometry
