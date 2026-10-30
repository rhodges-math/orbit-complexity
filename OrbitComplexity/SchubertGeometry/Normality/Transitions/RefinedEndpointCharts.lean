import OrbitComplexity.SchubertGeometry.BSDH.EndpointCharts

/-! # Refinements of the original append endpoint chart -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

private theorem product_square {S : Scheme.{u}} {V U Z : Over S} (d : V ⟶ U) :
    IsPullback (fst V Z) (d ⊗ₘ 𝟙 Z) d (fst U Z) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd U Z)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t ↦ t ≫ snd U Z) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

/-- Pulling the chosen chart along a refinement retains that exact chart and both
its append pullback and bundle-endpoint equations. -/
theorem refined_append_chart {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) {V U : Over (Spec (.of K))}
    (b : U ⟶ Over.mk (bsdhToSpec G word)) (d : V ⟶ U)
    (g : G.points) (a : U ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (c : U ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hcart : IsPullback
      (fst U (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      c.left b.left (bsdhAppendFst G word i))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ g) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    let cV := (d ⊗ₘ 𝟙 Y.toOver) ≫ c
    IsPullback (fst V Y.toOver).left cV.left (d.left ≫ b.left)
      (bsdhAppendFst G word i) ∧
    cV.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G Y) =
        ((d ≫ a) ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g := by
  dsimp only
  constructor
  · exact ((product_square (Z := (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) d).map
        (Over.forget (Spec (.of K)))).paste_vert hcart
  · change (d ⊗ₘ 𝟙 _).left ≫ c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd _ _ = _
    rw [hend]
    rw [← Category.assoc, ← Over.comp_left, tensorHom_comp_tensorHom, Category.comp_id]

end SchubertGeometry
