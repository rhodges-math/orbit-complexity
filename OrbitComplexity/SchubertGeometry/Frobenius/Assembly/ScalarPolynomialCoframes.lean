import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoverCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial coframes from retained affine coframes

The coframes retained on the tensor charts are transported to the chosen
common cover and glued on a whole polynomial chart. The comparison uses
the same original line module and the same polynomial coframe.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.OperatorSheaf
open scoped TensorProduct

open private scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private compared_append_frame frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private wholeComparison comparedWholeFrame comparedFineFrame polynomialFineCoframe
  polynomialCover_map polynomialFine_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private square_a_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframePairs

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem inverse_app {C D : Type u} [Category C] [Category D]
    {F G : C ⥤ D} (E : F ≅ G) (L : C) : E.symm.app L = (E.app L).symm := rfl

private theorem compose_frame {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) {L₀ L₁ L₂ : C} {M₃ M₄ M₅ : D}
    (H : L₀ ≅ L₁) (E : L₁ ≅ L₂) (i : F.obj L₂ ≅ M₃)
    (j : M₃ ≅ M₄) (t : M₄ ≅ M₅) :
    F.mapIso H ≪≫ F.mapIso E ≪≫ i ≪≫ j ≪≫ t =
      F.mapIso (H ≪≫ E) ≪≫ i ≪≫ j ≪≫ t := by
  simp only [Functor.mapIso_trans, Iso.trans_assoc]

private theorem coframe_word_square {A : Type u} [CommRing A]
    {Y YT YK Z PK B : Scheme.{u}}
    (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y) (hbase : n ≫ q = m)
    (r : YK ⟶ Z) (g : PK ⟶ YK) (c : PK ⟶ Z) (hc : g ≫ r = c)
    (aQ : Spec (.of A) ⟶ YK) (kF : Spec (.of A) ⟶ PK) (ha : kF ≫ g = aQ)
    (b : B ⟶ YT) (u : Spec (.of A) ⟶ B)
    (hs : u ≫ b = aQ ≫ n) (hs' : u ≫ b = (kF ≫ g) ≫ n)
    (hraw : aQ ≫ r = kF ≫ c)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK)
    (E : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback q).obj L) ≅ unitModule B)
    (he : squareFrameIso n aQ b u hs ((Scheme.Modules.pullback q).obj L) E =
      (Scheme.Modules.pullback aQ).mapIso
        ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫
          compared_append_frame m r aQ L LK EL kF c hraw Epoly) :
    squareFrameIso n (kF ≫ g) b u hs' ((Scheme.Modules.pullback q).obj L) E =
      comparedFineFrame r g kF c
        ((Category.assoc kF g r).trans (congrArg (fun t => kF ≫ t) hc))
        ((Scheme.Modules.pullback n).obj ((Scheme.Modules.pullback q).obj L)) LK
        (((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ EL) Epoly := by
  subst aQ
  exact he.trans (by
    simpa only [compared_append_frame, frame_on_composite, comparedFineFrame,
      inverse_app, Iso.trans_assoc] using
      compose_frame (Scheme.Modules.pullback (kF ≫ g))
        ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) EL
        ((pullbackComp (kF ≫ g) r).app LK) ((pullbackCongr hraw).app LK)
        (((pullbackComp kF c).app LK).symm ≪≫
          (Scheme.Modules.pullback kF).mapIso Epoly ≪≫ pullbackObjUnitIso kF))

private theorem domain_pullback {P Q X Y Z : Scheme.{u}}
    (I : Q ≅ P) (p : P ⟶ X) (a : P ⟶ Y) (f : X ⟶ Z) (n : Y ⟶ Z)
    (h : IsPullback p a f n) : IsPullback (I.hom ≫ p) (I.hom ≫ a) f n := by
  exact h.of_iso' I (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

private theorem refine_pullback {P X B PK YK YT : Scheme.{u}}
    (u : P ⟶ X) (a : P ⟶ YK) (f : X ⟶ YT) (n : YK ⟶ YT)
    (b : X ⟶ B) (v : B ⟶ YT) [Mono v] (z : PK ⟶ B) (g : PK ⟶ YK)
    (kF : P ⟶ PK) (hb : b ≫ v = f) (ha : kF ≫ g = a)
    (hP : IsPullback u a f n) (hV : IsPullback z g v n) :
    IsPullback u kF b z := by
  have hcomm : u ≫ b = kF ≫ z := by
    apply (cancel_mono v).1
    rw [Category.assoc, hb, hP.w, ← ha]
    simp only [Category.assoc, hV.w]
  have htotal : IsPullback u (kF ≫ g) (b ≫ v) n := by
    rw [ha, hb]
    exact hP
  exact htotal.of_bot hcomm hV

/-- Retained affine-chart coframes construct a whole polynomial-chart
coframe and its comparison, on the pulled original line module. -/
theorem exists_scalar_polynomial_coframe {S T K : Type u}
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
      (jB : ∀ w, Spec (.of (T ⊗[S] Γ(X w, ⊤))) ⟶ Y)
      (_hjB : ∀ w, (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        (X w).isoSpec.inv) ≫ old w = jB w)
      (v : ∀ w, Spec Γ(P w, ⊤) ⟶ Spec (.of (T ⊗[S] Γ(X w, ⊤))))
      (_hv : ∀ w, v w = Spec.map (CommRingCat.ofHom (scalarMap (R := T) (e w))))
      (aQ : ∀ w, Spec Γ(P w, ⊤) ⟶ YK)
      (_haQ : ∀ w, (P w).isoSpec.inv ≫ a w = aQ w)
      (kF : ∀ w, Spec Γ(P w, ⊤) ⟶ PK) (_hkF : ∀ w, kF w ≫ g = aQ w)
      (hraw : ∀ w, aQ w ≫ r = kF w ≫ c)
      (E : ∀ w, (Scheme.Modules.pullback (jB w)).obj L ≅
        unitModule (Spec (.of (T ⊗[S] Γ(X w, ⊤)))))
      (htotal : ∀ w, v w ≫ jB w = aQ w ≫ m)
      (_hcompare : ∀ w, squareFrameIso m (aQ w) (jB w) (v w) (htotal w) L (E w) =
        compared_append_frame m r (aQ w) L LK EL (kF w) c (hraw w) Epoly),
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
  intro e he jB hjB v hv aQ haQ kF hkF hraw E htotal hcompare
  have hchart (w : W.I₀) := exists_scalar_cover_coframe base baseT baseK q n m hbase hq hn.w
    (old w) ((appendCommonCover W V).f ⟨w, v₀⟩) (model w) (hC w) (a w) (p w) (hP w)
    (e w) (he w) (jB w) (hjB w) (v w) (hv w) (aQ w) (haQ w) L (E w)
    (compared_append_frame m r (aQ w) L LK EL (kF w) c (hraw w) Epoly)
    (htotal w) (hcompare w)
  choose k hkc hkf hcart hs ET hET using hchart
  let U := commonPolynomialCover W V v₀
  have hpoly (w : W.I₀) : IsPullback ((P w).isoSpec.inv ≫ k w) (kF w) (U.f w) z := by
    have hnew := domain_pullback (P w).isoSpec.symm (k w) (a w)
      ((appendCommonCover W V).f ⟨w, v₀⟩) n (hcart w)
    have hnative : kF w ≫ g = (P w).isoSpec.inv ≫ a w :=
      (hkF w).trans (haQ w).symm
    exact refine_pullback ((P w).isoSpec.inv ≫ k w) ((P w).isoSpec.inv ≫ a w)
      ((appendCommonCover W V).f ⟨w, v₀⟩) n (U.f w) (V.f v₀) z g (kF w)
      (polynomialCover_map W V v₀ w) hnative hnew hV
  have hword (w : W.I₀) : squareFrameIso n (kF w ≫ g)
      ((appendCommonCover W V).f ⟨w, v₀⟩) ((P w).isoSpec.inv ≫ k w)
      (polynomialFine_square W V v₀ w n g z hV.w (kF w)
        ((P w).isoSpec.inv ≫ k w) (hpoly w).w)
      ((Scheme.Modules.pullback q).obj L) (ET w) =
      comparedFineFrame r g (kF w) c
        ((Category.assoc (kF w) g r).trans (congrArg (fun t => kF w ≫ t) hc))
        ((Scheme.Modules.pullback n).obj ((Scheme.Modules.pullback q).obj L)) LK
        (((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ EL) Epoly := by
    exact coframe_word_square q n m hbase r g c hc (aQ w) (kF w) (hkF w)
      ((appendCommonCover W V).f ⟨w, v₀⟩) ((P w).isoSpec.inv ≫ k w) (hs w) _
      (hraw w) L LK EL Epoly (ET w) (hET w)
  refine ⟨ET, ?_⟩
  exact commonPolynomialCoframe_compare hT baseT W V v₀ n r g z hV.w
    (g ≫ baseK) (hV.paste_vert hn) c hc ((Scheme.Modules.pullback q).obj L) LK
    (((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ EL) Epoly
    (fun w => Spec Γ(P w, ⊤)) kF (fun w => (P w).isoSpec.inv ≫ k w) hpoly ET hword

end SchubertGeometry.RetainedCharacter
