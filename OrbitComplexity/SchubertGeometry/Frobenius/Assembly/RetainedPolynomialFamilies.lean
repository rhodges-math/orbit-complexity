import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCommonCoframes
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial coframes in every degree

Retained comparisons in every degree give polynomial coframes on one fixed
scheme and one fixed cover. The scheme, coefficient extension and chart maps
are chosen before the degree.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private adjustedFamilyData from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private compared_append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

namespace SchubertGeometry.RetainedCharacter

/-- Retained common-chart comparisons construct coframes in every degree on
the same polynomial cover over the same coefficient extension. -/
theorem retainedPolynomialCoframe_family {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (hT : Function.Injective (algebraMap T K))
    {Y YT YK Z : Scheme.{u}} [YT.IsSeparated]
    (base : Y ⟶ Spec (.of S)) (baseT : YT ⟶ Spec (.of T)) [Smooth baseT]
    (baseK : YK ⟶ Spec (.of K)) (q : YT ⟶ Y) (k : YK ⟶ YT) (m : YK ⟶ Y)
    (hbase : k ≫ q = m)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hk : IsPullback k baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (W V : YT.OpenCover.{u}) [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (PK : V.I₀ → Scheme.{u})
    (r : YK ⟶ Z) (g : ∀ v, PK v ⟶ YK) (z : ∀ v, PK v ⟶ V.X v)
    (hV : ∀ v, IsPullback (z v) (g v) (V.f v) k)
    (c : ∀ v, PK v ⟶ Z) (hc : ∀ v, g v ≫ r = c v)
    (L : ℕ → Y.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ n, (Scheme.Modules.pullback m).obj (L n) ≅
      (Scheme.Modules.pullback r).obj (LK n))
    (Epoly : ∀ n v, (Scheme.Modules.pullback (c v)).obj (LK n) ≅
      SheafOfModules.unit (PK v).ringCatSheaf)
    (X P : V.I₀ → W.I₀ → Scheme.{u})
    [∀ v w, IsAffine (X v w)] [∀ v w, IsAffine (P v w)]
    (old : ∀ v w, X v w ⟶ Y)
    (model : ∀ v w, (appendCommonCover W V).X ⟨w, v⟩ ⟶ X v w)
    (hC : ∀ v w, IsPullback (model v w) ((appendCommonCover W V).f ⟨w, v⟩)
      (old v w) q)
    (a : ∀ v w, P v w ⟶ YK) (p : ∀ v w, P v w ⟶ X v w)
    (hP : ∀ v w, IsPullback (p v w) (a v w) (old v w) m) :
    let : ∀ v w, Algebra S Γ(X v w, ⊤) := fun v w =>
      ((old v w ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : ∀ v w, Algebra K Γ(P v w, ⊤) := fun v w =>
      ((a v w ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (e : ∀ v w, K ⊗[S] Γ(X v w, ⊤) ≃ₐ[K] Γ(P v w, ⊤))
      (_he : ∀ v w x, e v w ((1 : K) ⊗ₜ[S] x) = (p v w).appTop.hom x)
      (j : ∀ v w, Spec Γ(X v w, ⊤) ⟶ Y)
      (_hj : ∀ v w, (X v w).isoSpec.inv ≫ old v w = j v w)
      (aQ : ∀ v w, Spec Γ(P v w, ⊤) ⟶ YK)
      (_haQ : ∀ v w, (P v w).isoSpec.inv ≫ a v w = aQ v w)
      (kF : ∀ v w, Spec Γ(P v w, ⊤) ⟶ PK v)
      (_hkF : ∀ v w, kF v w ≫ g v = aQ v w)
      (hraw : ∀ v w, aQ v w ≫ r = kF v w ≫ c v)
      (E : ∀ n v w, (Scheme.Modules.pullback (j v w)).obj (L n) ≅
        SheafOfModules.unit (Spec Γ(X v w, ⊤)).ringCatSheaf)
      (hscalar : ∀ v w, Spec.map (CommRingCat.ofHom
        ((e v w).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          j v w = aQ v w ≫ m)
      (_hretain : ∀ n v, adjustedFamilyData (R := T)
        (fun w => Γ(X v w, ⊤)) (fun w => Γ(P v w, ⊤)) (e v)
        (fun w => (e v w).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        m (L n) (j v) (aQ v) (hscalar v) (E n v)
        (fun w => compared_append_frame m r (aQ v w) (L n) (LK n) (EL n)
          (kF v w) (c v) (hraw v w) (Epoly n v))),
    ∀ n, scalarPolynomialCoframeFamily k r ((Scheme.Modules.pullback q).obj (L n))
      (LK n) (((pullbackComp k q).app (L n) ≪≫
        (pullbackCongr hbase).app (L n)) ≪≫ EL n)
      W V (fun v => v) PK g c hc (Epoly n) z (fun v => (hV v).w) := by
  intro algX algP e he j hj aQ haQ kF hkF hraw E hscalar hretain n v
  obtain ⟨d, hd, ET, hET⟩ := exists_retained_polynomial_coframe hT
    base baseT baseK q k m hbase hq hk W V v r (g v) (z v) (hV v) (c v) (hc v)
    (L n) (LK n) (EL n) (Epoly n v) (X v) (P v) (old v) (model v) (hC v)
    (a v) (p v) (hP v) (e v) (he v) (j v) (hj v) (aQ v) (haQ v)
    (kF v) (hkF v) (hraw v) (E n v) (hscalar v) (hretain n v)
  exact ⟨ET, hET⟩

end SchubertGeometry.RetainedCharacter
