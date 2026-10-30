import OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Morphism comparisons through two scalar extensions

Cartesian comparison maps through two successive pullbacks preserve a
morphism whenever their composites preserve the prescribed projections.
All identifications are made for arbitrary schemes over arbitrary bases.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace SchubertGeometry

open private scalar_comparison
  from OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage

private theorem double_scalar_comparison {B T U BK : Scheme.{u}}
    (κ : T ⟶ B) (τ : U ⟶ T) (ρ : BK ⟶ U)
    {X Y : Over B} {XK YK : Over BK} (f : X ⟶ Y) (g : XK ⟶ YK)
    (qX : XK.left ⟶ X.left) (qY : YK.left ⟶ Y.left)
    (mX : XK.left ⟶ pullback τ (pullback.fst κ X.hom))
    (mY : YK.left ⟶ pullback τ (pullback.fst κ Y.hom))
    (hX : IsPullback mX XK.hom (pullback.fst τ (pullback.fst κ X.hom)) ρ)
    (hY : IsPullback mY YK.hom (pullback.fst τ (pullback.fst κ Y.hom)) ρ)
    (hXo : mX ≫ pullback.snd τ (pullback.fst κ X.hom) ≫
      pullback.snd κ X.hom = qX)
    (hYo : mY ≫ pullback.snd τ (pullback.fst κ Y.hom) ≫
      pullback.snd κ Y.hom = qY)
    (h : qX ≫ f.left = g.left ≫ qY) :
    mX ≫ (chosenScalarArrow τ (chosenScalarArrow κ f)).left = g.left ≫ mY := by
  let X₁ : Over T := Over.mk (pullback.fst κ X.hom)
  let Y₁ : Over T := Over.mk (pullback.fst κ Y.hom)
  let qX₁ := mX ≫ pullback.snd τ X₁.hom
  let qY₁ := mY ≫ pullback.snd τ Y₁.hom
  have hX₁ : IsPullback qX₁ XK.hom X₁.hom (ρ ≫ τ) :=
    hX.paste_horiz (IsPullback.of_hasPullback τ X₁.hom).flip
  have hY₁ : IsPullback qY₁ YK.hom Y₁.hom (ρ ≫ τ) :=
    hY.paste_horiz (IsPullback.of_hasPullback τ Y₁.hom).flip
  have hX₁o : qX₁ ≫ pullback.snd κ X.hom = qX := by
    change (mX ≫ pullback.snd τ (pullback.fst κ X.hom)) ≫
      pullback.snd κ X.hom = qX
    simpa only [Category.assoc] using hXo
  have hY₁o : qY₁ ≫ pullback.snd κ Y.hom = qY := by
    change (mY ≫ pullback.snd τ (pullback.fst κ Y.hom)) ≫
      pullback.snd κ Y.hom = qY
    simpa only [Category.assoc] using hYo
  have hfirst := scalar_comparison κ (ρ ≫ τ) f g qX qY qX₁ qY₁
    hX₁ hY₁ hX₁o hY₁o h
  exact scalar_comparison τ ρ (chosenScalarArrow κ f) g qX₁ qY₁ mX mY
    hX hY rfl rfl hfirst

end SchubertGeometry
