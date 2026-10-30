import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.BSDH.Construction

/-!
# Products over BSDH flag patches

An appended correspondence is a product above each patch with a flag-chart lift.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry

universe u

private theorem tensor_fst_pullback {S : Scheme.{u}} {A B Y : Over S} (f : A ⟶ B) :
    IsPullback (fst A Y) (f ⊗ₘ 𝟙 Y) f (fst B Y) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd B Y)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t ↦ t ≫ snd B Y) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

/-- Over a flag chart containing an affine base patch, an appended
simple-Schubert correspondence is the product with its simple-Schubert fibre. -/
theorem bsdh_append_product_chart {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) (U : Over (Spec (.of K)))
    (b : U ⟶ Over.mk (bsdhToSpec G word)) [IsOpenImmersion b.left]
    (g : G.points) (a : U ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (hfactor : a.left ≫ flagSchemeChart G g = b.left ≫ bsdhMap G word) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ c : U ⊗ Y.toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])),
      IsPullback (fst U Y.toOver).left c.left b.left (bsdhAppendFst G word i) ∧
        IsOpenImmersion c.left := by
  dsimp only
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let F := flagBundleProjection G Y
  let p := (fst U Y.toOver).left
  let t := (a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g
  have hTensor : IsPullback (fst U Y.toOver).left (a ⊗ₘ 𝟙 Y.toOver).left a.left
      (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left :=
    (tensor_fst_pullback a).map (Over.forget (Spec (.of K)))
  have hFull : IsPullback p t (b.left ≫ bsdhMap G word) F := by
    rw [← hfactor]
    exact hTensor.paste_vert (flagBundlePullback G Y g)
  have hcond : (p ≫ b.left) ≫ bsdhMap G word = t ≫ F :=
    (Category.assoc _ _ _).trans hFull.w
  let φ := pullback.lift (p ≫ b.left) t hcond
  have houter : IsPullback p (φ ≫ pullback.snd (bsdhMap G word) F)
      (b.left ≫ bsdhMap G word) F := by
    simpa only [φ, pullback.lift_snd] using hFull
  have hraw : IsPullback p φ b.left (pullback.fst (bsdhMap G word) F) :=
    houter.of_bot (by simp only [φ, pullback.lift_fst])
      (IsPullback.of_hasPullback (bsdhMap G word) F)
  let e := (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i)
  let c := φ ≫ e.inv
  have hcart : IsPullback p c b.left (bsdhAppendFst G word i) :=
    hraw.of_iso' (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp [c]) (by simp) (by simp [e, bsdhAppendFst, F, Y])
  have hb : b.left ≫ bsdhToSpec G word = U.hom := b.w
  have hspec : c ≫ bsdhToSpec G (word ++ [i]) = (U ⊗ Y.toOver).hom := by
    have h := congrArg (fun f ↦ f ≫ bsdhToSpec G word) hcart.w
    simpa only [Category.assoc, bsdhAppendFst_toSpec, hb, p, (fst U Y.toOver).w] using h.symm
  refine ⟨Over.homMk c hspec, hcart, ?_⟩
  exact MorphismProperty.of_isPullback hcart inferInstance

end SchubertGeometry
