import OrbitComplexity.SchubertGeometry.BSDH.Construction
import OrbitComplexity.SchubertGeometry.BSDH.FiniteAtlas

/-!
# BSDH charts and bundle endpoints

Finite affine flag patches give product charts with their bundle-endpoint equations.
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

/-- A flag chart lift gives an append product chart preserving the bundle endpoint. -/
theorem bsdh_append_chart_endpoint {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) (U : Over (Spec (.of K)))
    (b : U ⟶ Over.mk (bsdhToSpec G word)) [IsOpenImmersion b.left]
    (g : G.points) (a : U ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (hfactor : a.left ≫ flagSchemeChart G g = b.left ≫ bsdhMap G word) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ c : U ⊗ Y.toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])),
      IsPullback (fst U Y.toOver).left c.left b.left (bsdhAppendFst G word i) ∧
        IsOpenImmersion c.left ∧
        c.left ≫ (bsdhAppendIso G word i).hom.left ≫
          pullback.snd (bsdhMap G word) (flagBundleProjection G Y) =
            (a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g := by
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
  refine ⟨Over.homMk c hspec, hcart, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback hcart inferInstance
  · change (φ ≫ e.inv) ≫ e.hom ≫ pullback.snd _ _ = t
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.lift_snd (p ≫ b.left) t hcond

private theorem patch_over {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)
    {X : Scheme.{u}} (b : X ⟶ bsdhScheme G word)
    (g : G.points) (a : X ⟶ (GroupActions.oppositeUnipotentVariety G).scheme)
    (ha : a ≫ flagSchemeChart G g = b ≫ bsdhMap G word) :
    a ≫ (GroupActions.oppositeUnipotentVariety G).toSpec = b ≫ bsdhToSpec G word := by
  have h := congrArg (fun f ↦ f ≫ flagSchemeToSpec G) ha
  have hc := flagSchemeChart_toSpec G g
  have hlocal : (a ≫ flagSchemeChart G g) ≫ flagSchemeToSpec G =
      a ≫ (GroupActions.oppositeUnipotentVariety G).toSpec :=
    (Category.assoc _ _ _).trans (congrArg (fun f ↦ a ≫ f) hc)
  have hbase : (b ≫ bsdhMap G word) ≫ flagSchemeToSpec G =
      b ≫ bsdhToSpec G word := Category.assoc _ _ _
  exact hlocal.symm.trans (h.trans hbase)

/-- A finite affine cover gives append charts with regular flag lifts and bundle endpoints. -/
theorem bsdh_finite_endpoint_cover {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
    (word : List G.rootBase.support) (i : G.rootBase.support) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ 𝒰 : (bsdhScheme G word).OpenCover.{u}, Finite 𝒰.I₀ ∧
      (∀ j, IsAffine (𝒰.X j)) ∧
      ∃ (g : 𝒰.I₀ → G.points)
        (a : ∀ j, Over.mk (𝒰.f j ≫ bsdhToSpec G word) ⟶
          (GroupActions.oppositeUnipotentVariety G).toOver),
        (∀ j, (a j).left ≫ flagSchemeChart G (g j) = 𝒰.f j ≫ bsdhMap G word) ∧
        ∀ j, ∃ c : Over.mk (𝒰.f j ≫ bsdhToSpec G word) ⊗ Y.toOver ⟶
            Over.mk (bsdhToSpec G (word ++ [i])),
          IsPullback (fst (Over.mk (𝒰.f j ≫ bsdhToSpec G word)) Y.toOver).left
            c.left (𝒰.f j) (bsdhAppendFst G word i) ∧
          IsOpenImmersion c.left ∧
          c.left ≫ (bsdhAppendIso G word i).hom.left ≫
            pullback.snd (bsdhMap G word) (flagBundleProjection G Y) =
              (a j ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y (g j) := by
  obtain ⟨𝒰, hfinite, haffine, g, a, ha⟩ := bsdh_finite_flag_cover G word
  let a' (j : 𝒰.I₀) : Over.mk (𝒰.f j ≫ bsdhToSpec G word) ⟶
      (GroupActions.oppositeUnipotentVariety G).toOver :=
    Over.homMk (a j) (patch_over G word (𝒰.f j) (g j) (a j) (ha j))
  refine ⟨𝒰, hfinite, haffine, g, a', ha, fun j ↦ ?_⟩
  let b : Over.mk (𝒰.f j ≫ bsdhToSpec G word) ⟶ Over.mk (bsdhToSpec G word) :=
    Over.homMk (𝒰.f j) rfl
  have : IsOpenImmersion b.left := 𝒰.map_prop j
  exact bsdh_append_chart_endpoint G word i _ b (g j) (a' j) (ha j)

end SchubertGeometry
