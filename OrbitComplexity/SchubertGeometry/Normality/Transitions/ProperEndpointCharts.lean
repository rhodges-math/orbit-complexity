import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorEndpointOpens
import OrbitComplexity.SchubertGeometry.Normality.Transitions.RefinedEndpointCharts

/-! # Original append charts over a refinement of the proper prior model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

/-- The original endpoint charts restrict to inverse images of a
finite affine cover on the same proper prior coefficient model. -/
theorem exists_proper_endpoint_charts {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (qY : bsdhScheme G word ⟶ Y)
    (h : IsPullback qY (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ j, IsAffine (U.X j))
    (V : (bsdhScheme G word).OpenCover.{u})
    (g : V.I₀ → G.points)
    (a : ∀ j, Over.mk (V.f j ≫ bsdhToSpec G word) ⟶
      (GroupActions.oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ flagSchemeChart G (g j) = V.f j ≫ bsdhMap G word)
    (c : ∀ j, Over.mk (V.f j ≫ bsdhToSpec G word) ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hcart : ∀ j, IsPullback
      (fst (Over.mk (V.f j ≫ bsdhToSpec G word))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      (c j).left (V.f j) (bsdhAppendFst G word i))
    (hend : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (g j)) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
        (qT : YT ⟶ Y) (mT : bsdhScheme G word ⟶ YT),
        IsProper baseT ∧ Smooth baseT ∧
        IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))) ∧
        IsPullback mT (bsdhToSpec G word) baseT
          (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
        mT ≫ qT = qY ∧
      ∃ (W : YT.OpenCover.{u}) (_ : Finite W.I₀) (_ : ∀ l, IsAffine (W.X l))
        (endpoint : W.I₀ → V.I₀),
        let O : W.I₀ → (bsdhScheme G word).Opens :=
          fun l ↦ mT ⁻¹ᵁ (W.f l).opensRange
        ∃ hcover : (⨆ l, O l) = ⊤,
          let VK := (bsdhScheme G word).openCoverOfIsOpenCover O hcover
          (∀ l, IsAffine (VK.X l)) ∧
          ∃ d : ∀ l, Over.mk (VK.f l ≫ bsdhToSpec G word) ⟶
              Over.mk (V.f (endpoint l) ≫ bsdhToSpec G word),
            (∀ l, (d l).left ≫ V.f (endpoint l) = VK.f l) ∧
            (∀ l, (d l ≫ a (endpoint l)).left ≫ flagSchemeChart G (g (endpoint l)) =
              VK.f l ≫ bsdhMap G word) ∧
            (∀ l, IsPullback
              (fst (Over.mk (VK.f l ≫ bsdhToSpec G word))
                (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
              ((d l ⊗ₘ 𝟙 _) ≫ c (endpoint l)).left (VK.f l) (bsdhAppendFst G word i)) ∧
            ∀ l, ((d l ⊗ₘ 𝟙 _) ≫ c (endpoint l)).left ≫
              (bsdhAppendIso G word i).hom.left ≫
                pullback.snd (bsdhMap G word) (flagBundleProjection G
                  (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
              ((d l ≫ a (endpoint l)) ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (g (endpoint l)) := by
  have Hprior := FrobeniusSplitting.exists_prior_endpoint_opens
    (K := K) (Y := Y) (YK := bsdhScheme G word)
    S hS base (bsdhToSpec G word) qY h U hU V
  obtain ⟨T, hST, Hprior⟩ := Hprior
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  obtain ⟨hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart, hmq, Hprior⟩ := Hprior
  obtain ⟨W, hfinite, haff, prior, endpoint, Hprior⟩ := Hprior
  let O : W.I₀ → (bsdhScheme G word).Opens := fun l ↦ mT ⁻¹ᵁ (W.f l).opensRange
  obtain ⟨hcover, hOaff, ar, br, qr, har, hbr, hqr, hqr', hcoverAll⟩ := Hprior
  let VK := (bsdhScheme G word).openCoverOfIsOpenCover O hcover
  let d (l : W.I₀) : Over.mk ((O l).ι ≫ bsdhToSpec G word) ⟶
      Over.mk (V.f (endpoint l) ≫ bsdhToSpec G word) :=
    Over.homMk (ar l) (by
      change ar l ≫ (V.f (endpoint l) ≫ bsdhToSpec G word) = _
      rw [← Category.assoc, har l]
      rfl)
  have hd (l : W.I₀) : (d l).left ≫ V.f (endpoint l) = (O l).ι := har l
  have ha' (l : W.I₀) : (d l ≫ a (endpoint l)).left ≫
      flagSchemeChart G (g (endpoint l)) = (O l).ι ≫ bsdhMap G word := by
    change (d l).left ≫ ((a (endpoint l)).left ≫ flagSchemeChart G (g (endpoint l))) = _
    calc
      _ = (d l).left ≫ (V.f (endpoint l) ≫ bsdhMap G word) :=
        congrArg (fun z : V.X (endpoint l) ⟶ (flagVariety G).scheme ↦ (d l).left ≫ z)
          (ha (endpoint l))
      _ = ((d l).left ≫ V.f (endpoint l)) ≫ bsdhMap G word :=
        (Category.assoc _ _ _).symm
      _ = (O l).ι ≫ bsdhMap G word :=
        congrArg (fun z : (O l).toScheme ⟶ bsdhScheme G word ↦ z ≫ bsdhMap G word) (hd l)
  let b (j : V.I₀) : Over.mk (V.f j ≫ bsdhToSpec G word) ⟶ Over.mk (bsdhToSpec G word) :=
    Over.homMk (V.f j) rfl
  have H (l : W.I₀) := refined_append_chart G word i
    (b (endpoint l)) (d l) (g (endpoint l))
    (a (endpoint l)) (c (endpoint l)) (hcart (endpoint l)) (hend (endpoint l))
  refine ⟨T, hST, ?_⟩
  refine ⟨hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart, hmq, ?_⟩
  refine ⟨W, hfinite, haff, endpoint, hcover, ?_⟩
  refine ⟨hOaff, d, hd, ha', ?_, ?_⟩
  · intro l
    have HC : IsPullback
        (fst (Over.mk ((O l).ι ≫ bsdhToSpec G word))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
        ((d l ⊗ₘ 𝟙 _) ≫ c (endpoint l)).left
        ((d l).left ≫ V.f (endpoint l)) (bsdhAppendFst G word i) := (H l).1
    exact (congrArg (fun z : (O l).toScheme ⟶ bsdhScheme G word ↦
      IsPullback
        (fst (Over.mk ((O l).ι ≫ bsdhToSpec G word))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
        ((d l ⊗ₘ 𝟙 _) ≫ c (endpoint l)).left z (bsdhAppendFst G word i)) (hd l)).mp HC
  · intro l
    exact (H l).2

end SchubertGeometry
