import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarNodeOverlaps
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorCoverExt
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Operator agreement on scalar node intersections

The original cocone supplies the overlap refinement cover. Naturality on its
specified scalar transitions then gives equality of the operators on the
entire node intersection, including the charts meeting infinity.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

namespace SchubertGeometry

open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

/-- Operators natural under the scalar node transitions agree on their whole
intersection, using the common refinements of the original cocone. -/
theorem scalarNodeOperators_agree {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    (D : Jᵒᵖ ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (D.map f)]
    [(D ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone D) (hc : IsColimit c) {Y : Scheme.{u}} (q : Y ⟶ c.pt)
    (P : J → Scheme.{u}) (r : ∀ s, P s ⟶ D.obj (op s)) (K : ∀ s, P s ⟶ Y)
    [∀ s, IsOpenImmersion (K s)]
    (hcart : ∀ s, IsPullback (r s) (K s) (c.ι.app (op s)) q)
    (g : ∀ {s t : J}, (s ⟶ t) → (P t ⟶ P s))
    [hG : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (g f)]
    (hg : ∀ {s t} (f : s ⟶ t), g f ≫ K s = K t)
    {p : ℕ} (φ : ∀ s, SchemeFrobeniusMap (P s) p)
    (hφ : ∀ {s t} (f : s ⟶ t), (φ s).openPullback (g f) = φ t)
    (s t : J) :
    (φ s).openPullback (pullback.fst (K s) (K t)) =
      (φ t).openPullback (pullback.snd (K s) (K t)) := by
  let V := scalarNodeOverlapCover D c hc q P r K hcart g hg s t
  apply SchemeFrobeniusMap.eq_of_openCover V
  intro a
  have hl : ((φ s).openPullback (pullback.fst (K s) (K t))).openPullback (V.f a) = φ a.1 := by
    have h₁ := (φ s).openPullback_comp (V.f a) (pullback.fst (K s) (K t))
    have h₂ := @pullback_eq_of_hom_eq p _ _ (φ s)
      (V.f a ≫ pullback.fst (K s) (K t))
      (g (s := s) (t := a.1) a.2.1) inferInstance (hG a.2.1)
      (scalarNodeOverlapCover_fst D c hc q P r K hcart g hg s t a)
    have h₃ := hφ (s := s) (t := a.1) a.2.1
    exact h₁.symm.trans (h₂.trans h₃)
  have hr : ((φ t).openPullback (pullback.snd (K s) (K t))).openPullback (V.f a) = φ a.1 := by
    have h₁ := (φ t).openPullback_comp (V.f a) (pullback.snd (K s) (K t))
    have h₂ := @pullback_eq_of_hom_eq p _ _ (φ t)
      (V.f a ≫ pullback.snd (K s) (K t))
      (g (s := t) (t := a.1) a.2.2) inferInstance (hG a.2.2)
      (scalarNodeOverlapCover_snd D c hc q P r K hcart g hg s t a)
    have h₃ := hφ (s := t) (t := a.1) a.2.2
    exact h₁.symm.trans (h₂.trans h₃)
  exact hl.trans hr.symm

end SchubertGeometry
