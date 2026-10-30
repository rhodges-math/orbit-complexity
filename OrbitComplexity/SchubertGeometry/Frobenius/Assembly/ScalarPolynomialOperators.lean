import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarNodeOperators
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Operators on polynomial intersections

The maps from polynomial charts to their projective nodes determine a map of
intersections. The operator agreement on the entire node intersection therefore
restricts to the prescribed polynomial chart intersection.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

namespace SchubertGeometry

open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

private theorem chartOperators_agree {A B P Q Y : Scheme.{u}}
    (K : P ⟶ Y) (L : Q ⟶ Y) [IsOpenImmersion K] [IsOpenImmersion L]
    (k : A ⟶ Y) (l : B ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion l]
    (a : A ⟶ P) (b : B ⟶ Q) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ K = k) (hb : b ≫ L = l) {p : ℕ}
    (φ : SchemeFrobeniusMap P p) (ψ : SchemeFrobeniusMap Q p)
    (ξ : SchemeFrobeniusMap A p) (η : SchemeFrobeniusMap B p)
    (hξ : ξ = φ.openPullback a) (hη : η = ψ.openPullback b)
    (hnode : φ.openPullback (pullback.fst K L) = ψ.openPullback (pullback.snd K L)) :
    ξ.openPullback (pullback.fst k l) = η.openPullback (pullback.snd k l) := by
  have hc : (pullback.fst k l ≫ a) ≫ K = (pullback.snd k l ≫ b) ≫ L := by
    simpa only [Category.assoc, ha, hb] using (pullback.condition (f := k) (g := l))
  let m : pullback k l ⟶ pullback K L :=
    pullback.lift (pullback.fst k l ≫ a) (pullback.snd k l ≫ b) hc
  have hm₁ : m ≫ pullback.fst K L = pullback.fst k l ≫ a := by
    exact pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd K L = pullback.snd k l ≫ b := by
    exact pullback.lift_snd _ _ _
  let : IsOpenImmersion (m ≫ pullback.fst K L) := by
    rw [hm₁]
    infer_instance
  let : IsOpenImmersion m := IsOpenImmersion.of_comp m (pullback.fst K L)
  calc
    ξ.openPullback (pullback.fst k l) =
        (φ.openPullback a).openPullback (pullback.fst k l) := by rw [hξ]
    _ = φ.openPullback (pullback.fst k l ≫ a) :=
      (φ.openPullback_comp (pullback.fst k l) a).symm
    _ = φ.openPullback (m ≫ pullback.fst K L) := pullback_eq_of_hom_eq φ hm₁.symm
    _ = (φ.openPullback (pullback.fst K L)).openPullback m :=
      φ.openPullback_comp m (pullback.fst K L)
    _ = (ψ.openPullback (pullback.snd K L)).openPullback m :=
      congrArg (fun Φ : SchemeFrobeniusMap (pullback K L) p => Φ.openPullback m) hnode
    _ = ψ.openPullback (m ≫ pullback.snd K L) :=
      (ψ.openPullback_comp m (pullback.snd K L)).symm
    _ = ψ.openPullback (pullback.snd k l ≫ b) := pullback_eq_of_hom_eq ψ hm₂
    _ = (ψ.openPullback b).openPullback (pullback.snd k l) :=
      ψ.openPullback_comp (pullback.snd k l) b
    _ = η.openPullback (pullback.snd k l) := by rw [hη]

/-- Operators on prescribed polynomial charts agree on their intersection when
node transition naturality is retained on the original cocone. The node overlap
cover and the map between the two intersections are constructed in the proof. -/
theorem scalarPolynomialOperators_agree {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    (D : Jᵒᵖ ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (D.map f)]
    [(D ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone D) (hc : IsColimit c) {Y : Scheme.{u}} (q : Y ⟶ c.pt)
    (P : J → Scheme.{u}) (r : ∀ s, P s ⟶ D.obj (op s)) (K : ∀ s, P s ⟶ Y)
    [∀ s, IsOpenImmersion (K s)]
    (hcart : ∀ s, IsPullback (r s) (K s) (c.ι.app (op s)) q)
    (g : ∀ {s t : J}, (s ⟶ t) → (P t ⟶ P s))
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion (g f)]
    (hg : ∀ {s t} (f : s ⟶ t), g f ≫ K s = K t)
    {p : ℕ} (φ : ∀ s, SchemeFrobeniusMap (P s) p)
    (hφ : ∀ {s t} (f : s ⟶ t), (φ s).openPullback (g f) = φ t)
    (s t : J) {A B : Scheme.{u}}
    (k : A ⟶ Y) (l : B ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion l]
    (a : A ⟶ P s) (b : B ⟶ P t) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ K s = k) (hb : b ≫ K t = l)
    (ξ : SchemeFrobeniusMap A p) (η : SchemeFrobeniusMap B p)
    (hξ : ξ = (φ s).openPullback a) (hη : η = (φ t).openPullback b) :
    ξ.openPullback (pullback.fst k l) = η.openPullback (pullback.snd k l) := by
  exact chartOperators_agree (K s) (K t) k l a b ha hb (φ s) (φ t) ξ η hξ hη
    (scalarNodeOperators_agree D c hc q P r K hcart g hg φ hφ s t)

end SchubertGeometry
