import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorCharts
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorGluing
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Equality of Frobenius operators on an open cover -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory

namespace FrobeniusSplitting.SchemeFrobeniusMap

open private sections_ext from OrbitComplexity.FrobeniusSplitting.Splittings.OperatorGluing

private theorem openPullback_map_eq {A X : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) {f g : A ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    φ.openPullback f = φ.openPullback g := by
  cases h
  rfl

private theorem range_restriction {A X : Scheme.{u}} {p : ℕ}
    (j : A ⟶ X) [IsOpenImmersion j] (φ : SchemeFrobeniusMap X p) :
    (φ.restrict j.opensRange).openPullback j.isoOpensRange.hom = φ.openPullback j := by
  rw [← φ.openPullback_restrict, ← φ.openPullback_comp]
  exact openPullback_map_eq φ j.isoOpensRange_hom_ι

/-- Frobenius operators agree when they agree on the charts of an open cover. -/
theorem eq_of_openCover {X : Scheme.{u}} {p : ℕ} (U : X.OpenCover.{u})
    (φ ψ : SchemeFrobeniusMap X p)
    (h : ∀ i, φ.openPullback (U.f i) = ψ.openPullback (U.f i)) : φ = ψ := by
  have hr (i : U.I₀) : φ.restrict (U.f i).opensRange = ψ.restrict (U.f i).opensRange := by
    apply (operatorIsoEquiv (U.f i).isoOpensRange).symm.injective
    exact (range_restriction (U.f i) φ).trans ((h i).trans (range_restriction (U.f i) ψ).symm)
  apply SchemeFrobeniusMap.ext
  intro W s
  apply sections_ext (fun i => (U.f i).opensRange) U.iSup_opensRange W
  intro i
  let V := W ⊓ (U.f i).opensRange
  have hv := congrArg (fun θ : SchemeFrobeniusMap (U.f i).opensRange.toScheme p =>
    θ.onSubopen V (inf_le_right : V ≤ (U.f i).opensRange)) (hr i)
  have heq : φ.onOpen V = ψ.onOpen V :=
    (φ.restrict_onSubopen (U.f i).opensRange V inf_le_right).symm.trans
      (hv.trans (ψ.restrict_onSubopen (U.f i).opensRange V inf_le_right))
  have ha := congrArg (fun f : FrobeniusLinearMap Γ(X, V) p =>
    f (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : V ≤ W)).op s)) heq
  exact (φ.restrict_comm (inf_le_left : V ≤ W) s).symm.trans
    (ha.trans (ψ.restrict_comm (inf_le_left : V ≤ W) s))

end FrobeniusSplitting.SchemeFrobeniusMap
