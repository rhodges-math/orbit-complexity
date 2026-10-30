import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.BSDH.FiniteAtlas
import OrbitComplexity.SchubertGeometry.BSDH.ProductCharts

/-!
# Finite BSDH bundle covers

The append preimages form a finite cover with product and projection comparisons.
-/

open CategoryTheory AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

namespace SchubertGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)

private theorem patch_over {X : Scheme.{u}} (b : X ⟶ bsdhScheme G word)
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

private theorem patch_product (i : G.rootBase.support) {X : Scheme.{u}}
    (b : X ⟶ bsdhScheme G word) [IsOpenImmersion b]
    (g : G.points) (a : X ⟶ (GroupActions.oppositeUnipotentVariety G).scheme)
    (ha : a ≫ flagSchemeChart G g = b ≫ bsdhMap G word) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ c : Over.mk (b ≫ bsdhToSpec G word) ⊗ Y.toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])),
      IsPullback (fst (Over.mk (b ≫ bsdhToSpec G word)) Y.toOver).left c.left b
          (bsdhAppendFst G word i) ∧ IsOpenImmersion c.left := by
  let U := Over.mk (b ≫ bsdhToSpec G word)
  let b' : U ⟶ Over.mk (bsdhToSpec G word) := Over.homMk b rfl
  let a' : U ⟶ (GroupActions.oppositeUnipotentVariety G).toOver :=
    Over.homMk a (patch_over G word b g a ha)
  have : IsOpenImmersion b'.left := inferInstanceAs (IsOpenImmersion b)
  have hf : a'.left ≫ flagSchemeChart G g = b'.left ≫ bsdhMap G word := ha
  exact bsdh_append_product_chart G word i U b' g a' hf

private theorem patch_preimage (i : G.rootBase.support) {X : Scheme.{u}}
    (b : X ⟶ bsdhScheme G word) [IsOpenImmersion b]
    (g : G.points) (a : X ⟶ (GroupActions.oppositeUnipotentVariety G).scheme)
    (ha : a ≫ flagSchemeChart G g = b ≫ bsdhMap G word) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    let P := Over.mk (b ≫ bsdhToSpec G word) ⊗ Y.toOver
    ∃ e : P.left ≅ Limits.pullback (bsdhAppendFst G word i) b,
      e.hom ≫ Limits.pullback.snd _ _ =
        (fst (Over.mk (b ≫ bsdhToSpec G word)) Y.toOver).left ∧
      IsPullback (fst (Over.mk (b ≫ bsdhToSpec G word)) Y.toOver).left
        (e.hom ≫ Limits.pullback.fst _ _) b (bsdhAppendFst G word i) ∧
      e.hom ≫ Limits.pullback.fst _ _ ≫ bsdhToSpec G (word ++ [i]) = P.hom := by
  obtain ⟨c, hcart, _⟩ := patch_product G word i b g a ha
  let e := hcart.flip.isoPullback
  have hf : e.hom ≫ Limits.pullback.fst _ _ = c.left :=
    hcart.flip.isoPullback_hom_fst
  have hp : e.hom ≫ Limits.pullback.snd _ _ =
      (fst (Over.mk (b ≫ bsdhToSpec G word)) _).left :=
    hcart.flip.isoPullback_hom_snd
  have hc := (congrArg (fun f ↦ IsPullback
      (fst (Over.mk (b ≫ bsdhToSpec G word)) _).left f b
        (bsdhAppendFst G word i)) hf).mpr hcart
  have hs : e.hom ≫ Limits.pullback.fst _ _ ≫ bsdhToSpec G (word ++ [i]) =
      (Over.mk (b ≫ bsdhToSpec G word) ⊗ _).hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ bsdhToSpec G (word ++ [i])) hf).trans c.w)
  exact ⟨e, hp, hc, hs⟩

/-- Pulling back a finite affine base cover along an appended correspondence gives
a finite open cover with product preimages and their structure-map equations. -/
theorem bsdh_finite_bundle_cover (i : G.rootBase.support) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ 𝒰 : (bsdhScheme G word).OpenCover.{u}, Finite 𝒰.I₀ ∧
      (∀ j, IsAffine (𝒰.X j)) ∧
      let 𝒲 := 𝒰.pullback₁ (bsdhAppendFst G word i)
      Finite 𝒲.I₀ ∧ ∀ j : 𝒰.I₀,
        ∃ e : (Over.mk (𝒰.f j ≫ bsdhToSpec G word) ⊗ Y.toOver).left ≅ 𝒲.X j,
          e.hom ≫ 𝒰.pullbackHom (bsdhAppendFst G word i) j =
            (fst (Over.mk (𝒰.f j ≫ bsdhToSpec G word)) Y.toOver).left ∧
          IsPullback (fst (Over.mk (𝒰.f j ≫ bsdhToSpec G word)) Y.toOver).left
            (e.hom ≫ 𝒲.f j) (𝒰.f j) (bsdhAppendFst G word i) ∧
          e.hom ≫ 𝒲.f j ≫ bsdhToSpec G (word ++ [i]) =
            (Over.mk (𝒰.f j ≫ bsdhToSpec G word) ⊗ Y.toOver).hom := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  obtain ⟨𝒰, hfinite, haffine, g, a, ha⟩ := bsdh_finite_flag_cover G word
  let 𝒲 := 𝒰.pullback₁ (bsdhAppendFst G word i)
  have hW : Finite 𝒲.I₀ := by
    change Finite 𝒰.I₀
    exact hfinite
  refine ⟨𝒰, hfinite, haffine, hW, fun j ↦ ?_⟩
  exact patch_preimage G word i (𝒰.f j) (g j) (a j) (ha j)

end SchubertGeometry
