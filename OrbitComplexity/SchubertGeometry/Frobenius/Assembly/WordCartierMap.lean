import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.NormalizedChartGluing
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ChartOperatorNormalization
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The normalized Cartier map on a word atlas

The original node cocone supplies the intersection cover. The prescribed raw
polynomial-chart maps are compared with the normalized node operators, so their
normalization and overlap agreement are consequences rather than gluing inputs.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private insertedLocal from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.NormalizedChartGluing
open private twistedOverMap_comp_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private range_restriction from
  OrbitComplexity.FrobeniusSplitting.Splittings.OperatorCoverExt

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A normalized operator on each projective node constructs the raw global
Cartier map on the original matching line. Only the prescribed node transitions
and ordinary polynomial-chart coordinate equations are used: local normalization
and pairwise agreement are derived internally. The inserted global operator
pulls back to those same node operators. -/
theorem exists_word_cartier_map {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] (hp : 0 < p)
    {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    (D : Jᵒᵖ ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (D.map f)]
    [(D ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone D) (hc : IsColimit c) {X : Scheme.{u}} (q : X ⟶ c.pt)
    (P : J → Scheme.{u}) (r : ∀ s, P s ⟶ D.obj (op s)) (K : ∀ s, P s ⟶ X)
    [∀ s, IsOpenImmersion (K s)]
    (hcart : ∀ s, IsPullback (r s) (K s) (c.ι.app (op s)) q)
    (g : ∀ {s t : J}, (s ⟶ t) → (P t ⟶ P s))
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion (g f)]
    (hg : ∀ {s t} (f : s ⟶ t), g f ≫ K s = K t)
    (φ : ∀ s, SchemeFrobeniusMap (P s) p)
    (hφ : ∀ {s t} (f : s ⟶ t), (φ s).openPullback (g f) = φ t)
    (hφone : ∀ s, (φ s).onOpen ⊤ 1 = 1)
    (base : X ⟶ Spec (.of C)) (L : X.Modules) (m : unitModule X ⟶ L)
    (U : X.OpenCover.{u}) (σ : U.I₀ → J)
    (a : ∀ i, U.X i ⟶ P (σ i)) [∀ i, IsOpenImmersion (a i)]
    (ha : ∀ i, a i ≫ K (σ i) = U.f i)
    (E : ∀ i, L.over (U.f i).opensRange ≅ (unitModule X).over (U.f i).opensRange)
    (k : ∀ i, (frobeniusRestriction C p base L).over (U.f i).opensRange ⟶
      (unitModule X).over (U.f i).opensRange)
    (hchart : ∀ i,
      (openOperatorEquiv C p base (U.f i).opensRange
        (insertedLocal base L m (U.f i).opensRange (k i))).openPullback
          (U.f i).isoOpensRange.hom = (φ (σ i)).openPullback (a i)) :
    ∃ Θ : frobeniusRestriction C p base L ⟶ unitModule X,
      (∀ i, Θ.over (U.f i).opensRange = k i) ∧
      (∀ i, (twistedSectionOperator base L Θ
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).openPullback (U.f i) =
          (φ (σ i)).openPullback (a i)) ∧
      (twistedSectionOperator base L Θ
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).onOpen ⊤ 1 = 1 := by
  have hnorm : ∀ i (T : Over (U.f i).opensRange),
      ((k i).val.app (op T)).hom ((m.val.app (op T.left)).hom (1 : Γ(X, T.left))) =
        (1 : Γ(X, T.left)) := by
    intro i T
    have h := localOperator_one_of_chart base (U.f i).opensRange
      (insertedLocal base L m (U.f i).opensRange (k i)) (U.f i).isoOpensRange
      (a i) (φ (σ i)) (hφone (σ i)) (hchart i) T
    have hcomp := twistedOverMap_comp_apply base (unitModule X) L (unitModule X)
      (U.f i).opensRange (m.over (U.f i).opensRange) (k i) T (1 : Γ(X, T.left))
    exact hcomp.symm.trans h
  have hoverlap : ∀ i j,
      ((openOperatorEquiv C p base (U.f i).opensRange
        (insertedLocal base L m (U.f i).opensRange (k i))).openPullback
          (U.f i).isoOpensRange.hom).openPullback (pullback.fst (U.f i) (U.f j)) =
      ((openOperatorEquiv C p base (U.f j).opensRange
        (insertedLocal base L m (U.f j).opensRange (k j))).openPullback
          (U.f j).isoOpensRange.hom).openPullback (pullback.snd (U.f i) (U.f j)) := by
    intro i j
    exact SchubertGeometry.scalarPolynomialOperators_agree D c hc q P r K hcart g hg φ hφ
      (σ i) (σ j) (U.f i) (U.f j) (a i) (a j) (ha i) (ha j) _ _ (hchart i) (hchart j)
  obtain ⟨Θ, hΘ, hlocal, hnormΘ⟩ :=
    exists_normalized_chart_map hp base L m U E k hnorm hoverlap
  refine ⟨Θ, hΘ, ?_, hnormΘ⟩
  intro i
  let Φ := twistedSectionOperator base L Θ
    ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
  have h := congrArg
    (fun z : SchemeFrobeniusMap (U.f i).opensRange.toScheme p =>
      z.openPullback (U.f i).isoOpensRange.hom) (hlocal i)
  exact (range_restriction (U.f i) Φ).symm.trans (h.trans (hchart i))

end SchubertGeometry.ProjectiveCartier
