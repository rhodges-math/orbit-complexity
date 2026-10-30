import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCoframes
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Whole polynomial coframes from retained units

The retained units are used without a second coefficient extension. Their
adjusted coframes construct the coframe on the whole polynomial chart,
while the comparison equations of every power remain available.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private scalarMap extendedFrame adjustedFamilyData from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private compared_append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private wholeComparison comparedWholeFrame polynomialFineCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem extend_chart {C : Type u} [Category C] {A B X Y : C}
    (f : A ⟶ B) (i : B ⟶ X) (g : X ⟶ Y) (j : B ⟶ Y) (h : i ≫ g = j) :
    (f ≫ i) ≫ g = f ≫ j :=
  (Category.assoc f i g).trans (congrArg (fun t => f ≫ t) h)

/-- Use the retained units on their given coefficient stage to construct
whole polynomial coframes, retaining the comparison of every unit power. -/
theorem exists_retained_polynomial_coframe {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (hT : Function.Injective (algebraMap T K))
    {Y YT YK Z PK : Scheme.{u}} [YT.IsSeparated]
    (base : Y ⟶ Spec (.of S)) (baseT : YT ⟶ Spec (.of T)) [Smooth baseT]
    (baseK : YK ⟶ Spec (.of K)) (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y)
    (hbase : n ≫ q = m)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hn : IsPullback n baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (W V : YT.OpenCover.{u}) [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (v₀ : V.I₀) (r : YK ⟶ Z) (g : PK ⟶ YK) (z : PK ⟶ V.X v₀)
    (hV : IsPullback z g (V.f v₀) n) (c : PK ⟶ Z) (hc : g ≫ r = c)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK)
    (X P : W.I₀ → Scheme.{u}) [∀ w, IsAffine (X w)] [∀ w, IsAffine (P w)]
    (old : ∀ w, X w ⟶ Y)
    (model : ∀ w, (appendCommonCover W V).X ⟨w, v₀⟩ ⟶ X w)
    (hC : ∀ w, IsPullback (model w) ((appendCommonCover W V).f ⟨w, v₀⟩) (old w) q)
    (a : ∀ w, P w ⟶ YK) (p : ∀ w, P w ⟶ X w)
    (hP : ∀ w, IsPullback (p w) (a w) (old w) m) :
    let : ∀ w, Algebra S Γ(X w, ⊤) := fun w =>
      (((old w) ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : ∀ w, Algebra K Γ(P w, ⊤) := fun w =>
      (((a w) ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (e : ∀ w, K ⊗[S] Γ(X w, ⊤) ≃ₐ[K] Γ(P w, ⊤))
      (_he : ∀ w x, e w ((1 : K) ⊗ₜ[S] x) = (p w).appTop.hom x)
      (j : ∀ w, Spec Γ(X w, ⊤) ⟶ Y)
      (_hj : ∀ w, (X w).isoSpec.inv ≫ old w = j w)
      (aQ : ∀ w, Spec Γ(P w, ⊤) ⟶ YK)
      (_haQ : ∀ w, (P w).isoSpec.inv ≫ a w = aQ w)
      (kF : ∀ w, Spec Γ(P w, ⊤) ⟶ PK) (_hkF : ∀ w, kF w ≫ g = aQ w)
      (hraw : ∀ w, aQ w ≫ r = kF w ≫ c)
      (E : ∀ w, (Scheme.Modules.pullback (j w)).obj L ≅ unitModule (Spec Γ(X w, ⊤)))
      (hscalar : ∀ w, Spec.map (CommRingCat.ofHom
          ((e w).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j w = aQ w ≫ m)
      (_hretain : adjustedFamilyData (R := T) (fun w => Γ(X w, ⊤)) (fun w => Γ(P w, ⊤)) e
        (fun w => (e w).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        m L j aQ hscalar E
        (fun w => compared_append_frame m r (aQ w) L LK EL (kF w) c (hraw w) Epoly)),
    ∃ d : ∀ w, (T ⊗[S] Γ(X w, ⊤))ˣ,
      (∀ w t, scalarMap (R := T) (e w) ((d w : T ⊗[S] Γ(X w, ⊤)) ^ t) =
        (affineCoframeUnit Γ(P w, ⊤)
          (squareFrameIso m (aQ w) (j w) (Spec.map (CommRingCat.ofHom
            ((e w).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)))
            (hscalar w) L (E w))
          (compared_append_frame m r (aQ w) L LK EL (kF w) c (hraw w) Epoly) : Γ(P w, ⊤)) ^ t) ∧
      ∃ ET : ∀ w, (Scheme.Modules.pullback ((appendCommonCover W V).f ⟨w, v₀⟩)).obj
          ((Scheme.Modules.pullback q).obj L) ≅ unitModule ((commonPolynomialCover W V v₀).X w),
        polynomialCoframeComparison z (commonPolynomialCover W V v₀)
          ((Scheme.Modules.pullback (V.f v₀)).obj ((Scheme.Modules.pullback q).obj L))
          (polynomialFineCoframe W V v₀ ((Scheme.Modules.pullback q).obj L) ET)
          (wholeComparison n (V.f v₀) g z hV.w ((Scheme.Modules.pullback q).obj L) ≪≫
            comparedWholeFrame r g c hc
              ((Scheme.Modules.pullback n).obj ((Scheme.Modules.pullback q).obj L)) LK
              (((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ EL) Epoly) := by
  dsimp only
  let : ∀ w, Algebra S Γ(X w, ⊤) := fun w =>
    (((old w) ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ w, Algebra K Γ(P w, ⊤) := fun w =>
    (((a w) ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro e he j hj aQ haQ kF hkF hraw E hscalar hretain
  obtain ⟨d, _hd, hpow, hcomp⟩ := hretain
  let ι := fun w => (Algebra.TensorProduct.includeRight :
    Γ(X w, ⊤) →ₐ[S] T ⊗[S] Γ(X w, ⊤)).toRingHom
  let jB := fun w => Spec.map (CommRingCat.ofHom (ι w)) ≫ j w
  let EB := fun w => adjustedCoframe (extendedFrame (ι w) (j w) L (E w)) (d w)
  choose htotal hcompare using hcomp
  have hjB (w : W.I₀) : (Spec.map (CommRingCat.ofHom (ι w)) ≫ (X w).isoSpec.inv) ≫
      old w = jB w := extend_chart _ _ _ _ (hj w)
  obtain ⟨ET, hET⟩ := exists_scalar_polynomial_coframe hT base baseT baseK q n m hbase hq hn
    W V v₀ r g z hV c hc L LK EL Epoly X P old model hC a p hP e he jB hjB
    (fun w => Spec.map (CommRingCat.ofHom (scalarMap (R := T) (e w)))) (fun _ => rfl)
    aQ haQ kF hkF hraw EB htotal hcompare
  exact ⟨d, hpow, ET, hET⟩

end SchubertGeometry.RetainedCharacter
