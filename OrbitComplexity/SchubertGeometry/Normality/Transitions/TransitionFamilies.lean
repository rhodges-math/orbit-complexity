import OrbitComplexity.SchubertGeometry.Normality.Transitions.TransitionCore
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelNaturality

/-! # Compatible Borel factors on common affine chart intersections -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
noncomputable section
universe u v
namespace SchubertGeometry

private theorem factor_unique {K : Type u} [Field K] [IsAlgClosed K]
    (G : ReductiveGroupData K) {Z : Over (Spec (.of K))}
    (s t : Z ⟶ (reductiveVariety G).toOver)
    (b c : Z ⟶ (borelVariety G).toOver)
    (hb : s = t * (b ≫ borelInclusion G))
    (hc : s = t * (c ≫ borelInclusion G)) : b = c := by
  have : Mono (borelInclusion G) := Over.mono_of_mono_left (borelInclusion G)
  apply (cancel_mono (borelInclusion G)).mp
  exact mul_left_cancel (hb.symm.trans hc)

/-- The factors of specified append charts are natural and satisfy the cocycle. -/
theorem bsdh_transition_family {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) {J : Type v}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (V : J → Over (Spec (.of K)))
    (b : ∀ j, V j ⟶ Over.mk (bsdhToSpec G word))
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ V j)
    (hp : ∀ (s t : {s : Finset J // s.Nonempty}) (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (hb : ∀ s j hj k hk, p s j hj ≫ b j = p s k hk ≫ b k)
    (g : J → G.points)
    (a : ∀ j, V j ⟶ (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ flagSchemeChart G (g j) = (b j).left ≫ bsdhMap G word)
    (c : ∀ j, V j ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hc : ∀ j, (fst (V j) _).left ≫ (b j).left =
      (c j).left ≫ bsdhAppendFst G word i)
    (he : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (g j)) :
    let I := {s : Finset J // s.Nonempty}
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ beta : ∀ (s : I) (j : J) (_ : j ∈ s.val) (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver,
      (∀ s j hj k hk, (p s j hj ≫ a j) ≫ flagChartMap G (g j) =
        ((p s k hk ≫ a k) ≫ flagChartMap G (g k)) *
          (beta s j hj k hk ≫ borelInclusion G)) ∧
      (∀ s j hj k hk, (p s j hj ⊗ₘ 𝟙 Y.toOver) ≫ c j =
        (overlapTwist (Y := Y.toOver) (beta s j hj k hk)).hom ≫
          (p s k hk ⊗ₘ 𝟙 Y.toOver) ≫ c k) ∧
      (∀ (s t : I) (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
        beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
          (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk) ∧
      (∀ s j hj k hk l hl, beta s j hj l hl =
        beta s k hk l hl * beta s j hj k hk) ∧
      ∀ (s t : I) (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
        simpleBorelCoefficientMap G i (F.obj t)
            (beta t j ((leOfHom f) hj) k ((leOfHom f) hk)) =
          (F.map f).hom.comp
            (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)) := by
  classical
  let I := {s : Finset J // s.Nonempty}
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  have H (s : I) (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :=
    bsdh_chart_transition G word i (V j) (V k)
      ((algSpec (.of K)).obj (.op (F.obj s))) (b j) (b k)
      (p s j hj) (p s k hk) (hb s j hj k hk) (g j) (g k)
      (a j) (a k) (ha j) (ha k) (c j) (c k) (hc j) (hc k) (he j) (he k)
  choose beta hs hchart using H
  have hn (s t : I) (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val) :
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk := by
    let u := (algSpec (.of K)).map (F.map f).op
    have hh := congrArg (fun z ↦ u ≫ z) (hs s j hj k hk)
    dsimp only [u] at hh
    simp only [MonObj.comp_mul, ← Category.assoc, hp] at hh
    apply factor_unique G _ _ _ _ (hs t j ((leOfHom f) hj) k ((leOfHom f) hk))
    simpa only [Category.assoc] using hh
  refine ⟨beta, hs, hchart, hn, ?_, ?_⟩
  · intro s j hj k hk l hl
    apply factor_unique G _ _ _ _ (hs s j hj l hl)
    rw [MonObj.mul_comp, ← mul_assoc, ← hs s k hk l hl, ← hs s j hj k hk]
  · intro s t f j hj k hk
    rw [hn]
    exact (simpleBorelCoefficient_natural G i (F.obj s) (F.obj t)
      (F.map f).hom (beta s j hj k hk)).1

end SchubertGeometry
