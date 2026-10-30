import Mathlib.AlgebraicGeometry.Pullbacks
import Batteries.Tactic.Lint

/-! # The scalar square of the specified paired source

The and arithmetic endpoint maps are retained individually. Their
pullbacks have a scalar comparison with both original projection equations. No
geometric property is for either paired source.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

noncomputable section

universe u

/-- The pullback of the two specified endpoint maps has the coefficient
square induced by the three original scalar comparisons. In particular the
source is the raw paired pullback, rather than a product replacement. -/
theorem paired_model_scalar_pullback
    {S K X Y F X₀ Y₀ F₀ : Scheme.{u}}
    (κ : K ⟶ S) (a : X ⟶ K) (b : Y ⟶ K) (t : F ⟶ K)
    (a₀ : X₀ ⟶ S) (b₀ : Y₀ ⟶ S) (t₀ : F₀ ⟶ S)
    (f : X ⟶ F) (g : Y ⟶ F) (f₀ : X₀ ⟶ F₀) (g₀ : Y₀ ⟶ F₀)
    (hf : f ≫ t = a) (hg : g ≫ t = b)
    (hf₀ : f₀ ≫ t₀ = a₀) (hg₀ : g₀ ≫ t₀ = b₀)
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀) (qF : F ⟶ F₀)
    (hX : IsPullback qX a a₀ κ) (hY : IsPullback qY b b₀ κ)
    (hF : IsPullback qF t t₀ κ)
    (hfx : f ≫ qF = qX ≫ f₀) (hgy : g ≫ qF = qY ≫ g₀) :
    let q := pullback.map f g f₀ g₀ qX qY qF hfx hgy
    IsPullback q (pullback.fst f g ≫ a) (pullback.fst f₀ g₀ ≫ a₀) κ ∧
      q ≫ pullback.fst f₀ g₀ = pullback.fst f g ≫ qX ∧
      q ≫ pullback.snd f₀ g₀ = pullback.snd f g ≫ qY := by
  let q := pullback.map f g f₀ g₀ qX qY qF hfx hgy
  have hbase : pullback.fst f g ≫ a = pullback.snd f g ≫ b := by
    rw [← hf, ← hg, ← Category.assoc, pullback.condition, Category.assoc]
  have hbase₀ : pullback.fst f₀ g₀ ≫ a₀ = pullback.snd f₀ g₀ ≫ b₀ := by
    rw [← hf₀, ← hg₀, ← Category.assoc, pullback.condition, Category.assoc]
  have hqfst : q ≫ pullback.fst f₀ g₀ = pullback.fst f g ≫ qX := by
    simp only [q, pullback.map, pullback.lift_fst]
  have hqsnd : q ≫ pullback.snd f₀ g₀ = pullback.snd f g ≫ qY := by
    simp only [q, pullback.map, pullback.lift_snd]
  have postfst {T : Scheme.{u}} (v : T ⟶ pullback f g) :
      (v ≫ q) ≫ pullback.fst f₀ g₀ = (v ≫ pullback.fst f g) ≫ qX := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ v ≫ k) hqfst).trans (Category.assoc _ _ _).symm)
  have postsnd {T : Scheme.{u}} (v : T ⟶ pullback f g) :
      (v ≫ q) ≫ pullback.snd f₀ g₀ = (v ≫ pullback.snd f g) ≫ qY := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ v ≫ k) hqsnd).trans (Category.assoc _ _ _).symm)
  refine ⟨IsPullback.mk' ?_ ?_ ?_, hqfst, hqsnd⟩
  · rw [← Category.assoc, hqfst, Category.assoc, hX.w, Category.assoc]
  · intro T φ φ' hq hb
    apply pullback.hom_ext
    · apply hX.hom_ext
      · have H := congrArg (fun k : T ⟶ pullback f₀ g₀ ↦
          k ≫ pullback.fst f₀ g₀) hq
        exact ((postfst φ).symm.trans H).trans (postfst φ')
      · simpa only [Category.assoc] using hb
    · apply hY.hom_ext
      · have H := congrArg (fun k : T ⟶ pullback f₀ g₀ ↦
          k ≫ pullback.snd f₀ g₀) hq
        exact ((postsnd φ).symm.trans H).trans (postsnd φ')
      · simpa only [Category.assoc, hbase] using hb
  · intro T z k hz
    have hzY : (z ≫ pullback.snd f₀ g₀) ≫ b₀ = k ≫ κ := by
      simpa only [Category.assoc, ← hbase₀] using hz
    let x := hX.lift (z ≫ pullback.fst f₀ g₀) k hz
    let y := hY.lift (z ≫ pullback.snd f₀ g₀) k hzY
    have hxq : x ≫ qX = z ≫ pullback.fst f₀ g₀ := hX.lift_fst _ _ _
    have hxa : x ≫ a = k := hX.lift_snd _ _ _
    have hyq : y ≫ qY = z ≫ pullback.snd f₀ g₀ := hY.lift_fst _ _ _
    have hyb : y ≫ b = k := hY.lift_snd _ _ _
    have hxy : x ≫ f = y ≫ g := by
      apply hF.hom_ext
      · calc
          (x ≫ f) ≫ qF = (x ≫ qX) ≫ f₀ := by
            rw [Category.assoc, hfx, ← Category.assoc]
          _ = (z ≫ pullback.fst f₀ g₀) ≫ f₀ := by rw [hxq]
          _ = (z ≫ pullback.snd f₀ g₀) ≫ g₀ := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = (y ≫ qY) ≫ g₀ := by rw [hyq]
          _ = (y ≫ g) ≫ qF := by
            simpa only [Category.assoc] using congrArg (fun k ↦ y ≫ k) hgy.symm
      · rw [Category.assoc, hf, hxa, Category.assoc, hg, hyb]
    let l := pullback.lift x y hxy
    have hlfst : l ≫ pullback.fst f g = x := pullback.lift_fst _ _ _
    have hlsnd : l ≫ pullback.snd f g = y := pullback.lift_snd _ _ _
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · exact (postfst l).trans
          ((congrArg (fun k ↦ k ≫ qX) hlfst).trans hxq)
      · exact (postsnd l).trans
          ((congrArg (fun k ↦ k ≫ qY) hlsnd).trans hyq)
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ a) hlfst).trans hxa)

end
end FrobeniusSplitting
