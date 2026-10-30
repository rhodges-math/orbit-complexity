import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarChartCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retained coframes on a chosen scalar cover

A chart pullback constructs its field lift and tensor-coordinate
isomorphism. The retained coframe then gives a coframe of the same
original line on the scalar-cover chart.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open scoped TensorProduct

open private comparison_lift from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
open private scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem chart_structure {C : Type u} [Category C]
    {P XT YT YK BT BK : C} (k : P ⟶ XT) (f : XT ⟶ YT) (a : P ⟶ YK)
    (n : YK ⟶ YT) (t : YT ⟶ BT) (b : YK ⟶ BK) (κ : BK ⟶ BT)
    (hk : k ≫ f = a ≫ n) (hn : n ≫ t = b ≫ κ) :
    k ≫ (f ≫ t) = (a ≫ b) ≫ κ := by
  rw [← Category.assoc, hk, Category.assoc, hn, ← Category.assoc]

private theorem chart_projection {C : Type u} [Category C]
    {B XT X Y YT : C} (I : B ⟶ XT) (c : XT ⟶ X) (f : XT ⟶ YT)
    (g : X ⟶ Y) (q : YT ⟶ Y) (j : B ⟶ X) (jB : B ⟶ Y)
    (hc : c ≫ g = f ≫ q) (hI : I ≫ c = j) (hj : j ≫ g = jB) :
    I ≫ f ≫ q = jB := by
  rw [← hc, ← Category.assoc, hI, hj]

private theorem chart_field {C : Type u} [Category C] {P Q XT YT YK : C}
    (i : Q ⟶ P) (k : P ⟶ XT) (f : XT ⟶ YT) (a : P ⟶ YK)
    (n : YK ⟶ YT) (aQ : Q ⟶ YK) (hk : k ≫ f = a ≫ n)
    (ha : i ≫ a = aQ) : (i ≫ k) ≫ f = aQ ≫ n := by
  rw [Category.assoc, hk, ← Category.assoc, ha]

/-- A retained tensor-chart coframe constructs a coframe on the prescribed
scalar-cover chart, including its field lift and comparison equation. -/
theorem exists_scalar_cover_coframe {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {Y YT YK X XT P : Scheme.{u}} [IsAffine X] [IsAffine P]
    (base : Y ⟶ Spec (.of S)) (baseT : YT ⟶ Spec (.of T))
    (baseK : YK ⟶ Spec (.of K)) (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y)
    (hbase : n ≫ q = m)
    (hq : IsPullback q baseT base
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hn : n ≫ baseT = baseK ≫ Spec.map (CommRingCat.ofHom (algebraMap T K)))
    (g : X ⟶ Y) (f : XT ⟶ YT) (c : XT ⟶ X)
    (hC : IsPullback c f g q)
    (a : P ⟶ YK) (p : P ⟶ X) (hP : IsPullback p a g m) :
    let : Algebra S Γ(X, ⊤) :=
      ((g ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : Algebra K Γ(P, ⊤) :=
      ((a ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (e : K ⊗[S] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤))
      (_he : ∀ x, e ((1 : K) ⊗ₜ[S] x) = p.appTop.hom x)
      (jB : Spec (.of (T ⊗[S] Γ(X, ⊤))) ⟶ Y)
      (_hjB : (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
          X.isoSpec.inv) ≫ g = jB)
      (v : Spec Γ(P, ⊤) ⟶ Spec (.of (T ⊗[S] Γ(X, ⊤))))
      (_hv : v = Spec.map (CommRingCat.ofHom (scalarMap (R := T) e)))
      (aQ : Spec Γ(P, ⊤) ⟶ YK) (_haQ : P.isoSpec.inv ≫ a = aQ)
      (L : Y.Modules) (E : (Scheme.Modules.pullback jB).obj L ≅
        unitModule (Spec (.of (T ⊗[S] Γ(X, ⊤)))))
      (FK : (Scheme.Modules.pullback aQ).obj ((Scheme.Modules.pullback m).obj L) ≅
        unitModule (Spec Γ(P, ⊤)))
      (htotal : v ≫ jB = aQ ≫ m)
      (_hcompare : squareFrameIso m aQ jB v htotal L E = FK),
    ∃ (k : P ⟶ XT) (_hkc : k ≫ c = p) (_hkf : k ≫ f = a ≫ n)
      (_hcart : IsPullback k a f n)
      (hsquare : (P.isoSpec.inv ≫ k) ≫ f = aQ ≫ n)
      (ET : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback q).obj L) ≅
        unitModule XT),
      squareFrameIso n aQ f (P.isoSpec.inv ≫ k) hsquare
        ((Scheme.Modules.pullback q).obj L) ET =
        (Scheme.Modules.pullback aQ).mapIso
          ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ FK := by
  dsimp only
  let : Algebra S Γ(X, ⊤) :=
    ((g ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    ((a ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro e he jB hjB v hv aQ haQ L E FK htotal hcompare
  obtain ⟨k, hkc, hkf, hcart⟩ :=
    comparison_lift q n m hbase.symm g f c hC a p hP
  have hb : k ≫ (f ≫ baseT) = (a ≫ baseK) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T K)) :=
    chart_structure k f a n baseT baseK _ hkf hn
  obtain ⟨I, hIold, hIfield⟩ := exists_scalar_affine_chart
    (g ≫ base) (f ≫ baseT) (a ≫ baseK) c (hC.paste_vert hq) p k hkc hb e he
  have hmodel : I.hom ≫ f ≫ q = jB :=
    chart_projection I.hom c f g q _ jB hC.w hIold hjB
  have hfield : v ≫ I.hom = P.isoSpec.inv ≫ k := by
    rw [hv]
    exact hIfield
  have hsquare : (P.isoSpec.inv ≫ k) ≫ f = aQ ≫ n :=
    chart_field P.isoSpec.inv k f a n aQ hkf haQ
  obtain ⟨ET, hET⟩ := exists_scalar_chart_coframe q n m hbase jB f aQ v
    (P.isoSpec.inv ≫ k) I hmodel hfield hsquare htotal L E FK hcompare
  exact ⟨k, hkc, hkf, hcart, hsquare, ET, hET⟩

end SchubertGeometry.RetainedCharacter
