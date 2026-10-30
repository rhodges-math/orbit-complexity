import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframeFamilies
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedPolynomialFamilies
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Refinement of retained coframe families

Equations identifying the common-chart maps with their singleton refinements
are transported over arbitrary schemes. The two expressions for the append
coframe are identified as whole isomorphisms.
-/

set_option autoImplicit false

noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private coframeFamilyData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframeFamilies
open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private frame_on_composite compared_append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

namespace SchubertGeometry.RetainedCharacter

private theorem comparedFrame_eq {A : Type u} [CommRing A]
    {Y YK Z P : Scheme.{u}} (q : YK ⟶ Y) (r : YK ⟶ Z)
    (j : Spec (.of A) ⟶ YK) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (k : Spec (.of A) ⟶ P) (g : P ⟶ Z) (h : j ≫ r = k ≫ g)
    (E : (Scheme.Modules.pullback g).obj LK ≅ SheafOfModules.unit P.ringCatSheaf) :
    compared_append_frame q r j L LK EL k g h E =
      comparisonCoframe j r k g h ((Scheme.Modules.pullback q).obj L) LK EL E := by
  simp only [compared_append_frame, comparisonCoframe, frame_on_composite]
  rfl

/-- Identifying the common-chart maps with their refinements preserves the
retained units, all their powers and every adjusted coframe over the fixed ring. -/
theorem coframeFamily_refinement
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {I : Type v} (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra S (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[S] M l ≃ₐ[K] A l) (v₀ : ∀ l, M l →+* A l)
    {Y YK Z : Scheme.{u}} (q : YK ⟶ Y) (r : YK ⟶ Z)
    (L : ℕ → Y.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ n, (Scheme.Modules.pullback q).obj (L n) ≅
      (Scheme.Modules.pullback r).obj (LK n))
    (D C : I → Scheme.{u})
    (legN : ∀ l, D l ⟶ Y) (legF : ∀ l, C l ⟶ YK)
    (t : ∀ l, Spec (.of (M l)) ⟶ D l) (f : ∀ l, Spec (.of (A l)) ⟶ C l)
    (j : ∀ l, Spec (.of (M l)) ⟶ Y) (a : ∀ l, Spec (.of (A l)) ⟶ YK)
    (hj : ∀ l, j l = t l ≫ legN l) (ha : ∀ l, a l = f l ≫ legF l)
    (hs : ∀ l, Spec.map (CommRingCat.ofHom (v₀ l)) ≫ j l = a l ≫ q)
    (hs' : ∀ l, Spec.map (CommRingCat.ofHom (v₀ l)) ≫ (t l ≫ legN l) =
      (f l ≫ legF l) ≫ q)
    (P : I → Scheme.{u}) (k : ∀ l, Spec (.of (A l)) ⟶ P l)
    (c : ∀ l, P l ⟶ Z)
    (h : ∀ l, a l ≫ r = k l ≫ c l)
    (h' : ∀ l, (f l ≫ legF l) ≫ r = k l ≫ c l)
    (E : ∀ n l, (Scheme.Modules.pullback (legN l)).obj (L n) ≅
      SheafOfModules.unit (D l).ringCatSheaf)
    (F : ∀ n l, (Scheme.Modules.pullback (c l)).obj (LK n) ≅
      SheafOfModules.unit (P l).ringCatSheaf)
    (d : ∀ l, (T ⊗[S] M l)ˣ) :
    coframeFamilyData M A e v₀ q L j a hs
      (fun n l => frame_on_composite (t l) (legN l) (j l) (hj l) (L n) (E n l))
      (fun n l => compared_append_frame q r (a l) (L n) (LK n) (EL n)
        (k l) (c l) (h l) (F n l)) d ↔
    coframeFamilyData M A e v₀ q L (fun l => t l ≫ legN l)
      (fun l => f l ≫ legF l) hs'
      (fun n l => frame_on_composite (t l) (legN l) (t l ≫ legN l) rfl (L n) (E n l))
      (fun n l => comparisonCoframe (f l ≫ legF l) r (k l) (c l) (h' l)
        ((Scheme.Modules.pullback q).obj (L n)) (LK n) (EL n) (F n l)) d := by
  cases funext hj
  cases funext ha
  simp only [comparedFrame_eq]

end SchubertGeometry.RetainedCharacter
