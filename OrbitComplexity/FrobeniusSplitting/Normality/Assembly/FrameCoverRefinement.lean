import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorEndpointOpens
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Batteries.Tactic.Lint

/-! # A finite affine cover with both frame factorizations

After coefficient extension, the endpoint refinement is intersected with the
inverse image of the prescribed arithmetic cover. The scheme and its scalar
projection stay fixed during this intersection. The resulting affine charts
retain arithmetic maps to the prescribed charts and geometric maps to the
endpoint charts.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace FrobeniusSplitting

/-- A finite affine cover on the specified scheme, with both the arithmetic
chart factorization and the geometric endpoint factorization. -/
def frameCoverData {Y YK YT : Scheme.{u}}
    (qT : YT ⟶ Y) (mT : YK ⟶ YT) (qY : YK ⟶ Y)
    (U : Y.OpenCover.{u}) (V : YK.OpenCover.{u}) : Prop :=
  ∃ (W : YT.OpenCover.{u}) (_ : Finite W.I₀) (_ : ∀ l, IsAffine (W.X l))
    (prior : W.I₀ → U.I₀) (endpoint : W.I₀ → V.I₀)
    (b : ∀ l, W.X l ⟶ U.X (prior l))
    (a : ∀ l, pullback (W.f l) mT ⟶ V.X (endpoint l)),
    (∀ l, b l ≫ U.f (prior l) = W.f l ≫ qT) ∧
    (∀ l, a l ≫ V.f (endpoint l) = pullback.snd (W.f l) mT) ∧
    (∀ l, pullback.fst (W.f l) mT ≫ b l ≫ U.f (prior l) =
      pullback.snd (W.f l) mT ≫ qY) ∧
    (∀ l, IsAffine (pullback (W.f l) mT)) ∧
    ∀ (Z : Scheme.{u}) (g : Z ⟶ YT) (z : Z),
      ∃ l, ∃ x : (pullback (W.f l) g : Scheme.{u}),
        (pullback.snd (W.f l) g) x = z

private theorem affine_fibre_product {Y A B : Scheme.{u}} [Y.IsSeparated]
    [IsAffine A] [IsAffine B] (f : A ⟶ Y) (g : B ⟶ Y) :
    IsAffine (pullback f g) := by
  have hterminal : IsAffineHom (f ≫ terminal.from Y) := by
    rw [terminal.comp_from]
    infer_instance
  let : IsAffineHom (f ≫ terminal.from Y) := hterminal
  let : IsAffineHom f := IsAffineHom.of_comp f (terminal.from Y)
  infer_instance

private theorem endpoint_refinement {Y YK YT : Scheme.{u}} [Y.IsSeparated]
    (qT : YT ⟶ Y) (mT : YK ⟶ YT) [IsAffineHom mT] (qY : YK ⟶ Y)
    (hm : mT ≫ qT = qY)
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ i, IsAffine (U.X i))
    (V : YK.OpenCover.{u}) (W : YT.OpenCover.{u}) [Finite W.I₀]
    (hW : ∀ l, IsAffine (W.X l)) (endpoint : W.I₀ → V.I₀)
    (Q : W.I₀ → Scheme.{u}) (f : ∀ l, Q l ⟶ YK)
    (q : ∀ l, Q l ⟶ W.X l)
    (a : ∀ l, Q l ⟶ V.X (endpoint l))
    (hcart : ∀ l, IsPullback (q l) (f l) (W.f l) mT)
    (ha : ∀ l, a l ≫ V.f (endpoint l) = f l) :
    frameCoverData qT mT qY U V := by
  let B : YT.OpenCover.{u} := W.bind (fun l => U.pullback₂ (W.f l ≫ qT))
  have hfinite : Finite B.I₀ := by
    change Finite (Σ _ : W.I₀, U.I₀)
    infer_instance
  have haff (l : B.I₀) : IsAffine (B.X l) := by
    change IsAffine (pullback (U.f l.2) (W.f l.1 ≫ qT))
    let : IsAffine (U.X l.2) := hU l.2
    let : IsAffine (W.X l.1) := hW l.1
    exact affine_fibre_product (U.f l.2) (W.f l.1 ≫ qT)
  let r (l : B.I₀) : B.X l ⟶ W.X l.1 :=
    pullback.snd (U.f l.2) (W.f l.1 ≫ qT)
  let b (l : B.I₀) : B.X l ⟶ U.X l.2 :=
    pullback.fst (U.f l.2) (W.f l.1 ≫ qT)
  have hb (l : B.I₀) : b l ≫ U.f l.2 = B.f l ≫ qT :=
    (pullback.condition (f := U.f l.2) (g := W.f l.1 ≫ qT)).trans
      (Category.assoc _ _ _).symm
  have hw (l : B.I₀) :
      (pullback.fst (B.f l) mT ≫ r l) ≫ W.f l.1 =
        pullback.snd (B.f l) mT ≫ mT :=
    (Category.assoc _ _ _).trans (pullback.condition (f := B.f l) (g := mT))
  let lift (l : B.I₀) : pullback (B.f l) mT ⟶ Q l.1 :=
    (hcart l.1).lift (pullback.fst (B.f l) mT ≫ r l)
      (pullback.snd (B.f l) mT) (hw l)
  have hlift (l : B.I₀) : lift l ≫ f l.1 = pullback.snd (B.f l) mT :=
    (hcart l.1).lift_snd _ _ (hw l)
  have hep (l : B.I₀) : (lift l ≫ a l.1) ≫ V.f (endpoint l.1) =
      pullback.snd (B.f l) mT :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => lift l ≫ k) (ha l.1)).trans (hlift l))
  have hprior (l : B.I₀) :
      pullback.fst (B.f l) mT ≫ b l ≫ U.f l.2 =
        pullback.snd (B.f l) mT ≫ qY := by
    calc
      _ = pullback.fst (B.f l) mT ≫ B.f l ≫ qT :=
        congrArg (fun k => pullback.fst (B.f l) mT ≫ k) (hb l)
      _ = (pullback.snd (B.f l) mT ≫ mT) ≫ qT :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ qT) (pullback.condition (f := B.f l) (g := mT)))
      _ = pullback.snd (B.f l) mT ≫ qY :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => pullback.snd (B.f l) mT ≫ k) hm)
  have hfield (l : B.I₀) : IsAffine (pullback (B.f l) mT) := by
    let : IsAffine (B.X l) := haff l
    infer_instance
  exact ⟨B, hfinite, haff, (fun l => l.2), (fun l => endpoint l.1), b,
    (fun l => lift l ≫ a l.1), hb, hep, hprior, hfield,
    (fun Z g z => Scheme.Cover.exists_eq (B.pullback₂ g) z)⟩

end FrobeniusSplitting
