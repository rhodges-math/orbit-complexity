import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialOperators
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Operator agreement on intersections of chart images

The fibre product of two open charts is identified with the intersection of
their images. Agreement on that fibre product is therefore agreement of the
restricted operators on the ambient intersection.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

namespace SchubertGeometry

open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

private theorem operator_eq_at_inf {X : Scheme.{u}} {p : ℕ} {U V W : X.Opens}
    (φ : SchemeFrobeniusMap U.toScheme p) (ψ : SchemeFrobeniusMap V.toScheme p)
    (hW : W = U ⊓ V) (hU : W ≤ U) (hV : W ≤ V)
    (h : φ.openPullback (X.homOfLE hU) = ψ.openPullback (X.homOfLE hV)) :
    φ.openPullback (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) =
      ψ.openPullback (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) := by
  subst W
  exact h

/-- Agreement of the operators pulled to the prescribed chart fibre product
implies agreement on the intersection of their ambient open images. -/
theorem rangeOperators_agree {A B X : Scheme.{u}} {p : ℕ}
    (f : A ⟶ X) (g : B ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (φ : SchemeFrobeniusMap f.opensRange.toScheme p)
    (ψ : SchemeFrobeniusMap g.opensRange.toScheme p)
    (h : (φ.openPullback f.isoOpensRange.hom).openPullback (pullback.fst f g) =
      (ψ.openPullback g.isoOpensRange.hom).openPullback (pullback.snd f g)) :
    φ.openPullback (X.homOfLE (inf_le_left : f.opensRange ⊓ g.opensRange ≤ f.opensRange)) =
      ψ.openPullback (X.homOfLE (inf_le_right : f.opensRange ⊓ g.opensRange ≤ g.opensRange)) := by
  let q : pullback f g ⟶ X := pullback.fst f g ≫ f
  have hW : q.opensRange = f.opensRange ⊓ g.opensRange := by
    apply TopologicalSpace.Opens.ext
    exact IsOpenImmersion.range_pullback_to_base_of_left f g
  have hU : q.opensRange ≤ f.opensRange := hW.le.trans inf_le_left
  have hV : q.opensRange ≤ g.opensRange := hW.le.trans inf_le_right
  apply operator_eq_at_inf φ ψ hW hU hV
  apply (SchemeFrobeniusMap.operatorIsoEquiv q.isoOpensRange).symm.injective
  change (φ.openPullback (X.homOfLE hU)).openPullback q.isoOpensRange.hom =
    (ψ.openPullback (X.homOfLE hV)).openPullback q.isoOpensRange.hom
  have hleft : q.isoOpensRange.hom ≫ X.homOfLE hU =
      pullback.fst f g ≫ f.isoOpensRange.hom := by
    apply (cancel_mono f.opensRange.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
    rfl
  have hright : q.isoOpensRange.hom ≫ X.homOfLE hV =
      pullback.snd f g ≫ g.isoOpensRange.hom := by
    apply (cancel_mono g.opensRange.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
    exact pullback.condition
  have hl₁ := φ.openPullback_comp q.isoOpensRange.hom (X.homOfLE hU)
  have hl₂ := pullback_eq_of_hom_eq φ hleft
  have hl₃ := φ.openPullback_comp (pullback.fst f g) f.isoOpensRange.hom
  have hr₁ := ψ.openPullback_comp q.isoOpensRange.hom (X.homOfLE hV)
  have hr₂ := pullback_eq_of_hom_eq ψ hright
  have hr₃ := ψ.openPullback_comp (pullback.snd f g) g.isoOpensRange.hom
  exact (hl₁.symm.trans (hl₂.trans hl₃)).trans
    (h.trans (hr₁.symm.trans (hr₂.trans hr₃)).symm)

end SchubertGeometry
