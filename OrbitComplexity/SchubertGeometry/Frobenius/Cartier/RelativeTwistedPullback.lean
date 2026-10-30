import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import Batteries.Tactic.Lint

/-! # Cancellation of operator pullback along a chart isomorphism -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open FrobeniusSplitting
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

variable {p : ℕ}

private theorem pushforward_openPullback {X Y : Scheme.{u}} (e : X ≅ Y)
    (φ : SchemeFrobeniusMap X p) : (φ.pushforward e.hom).openPullback e.hom = φ := by
  apply SchemeFrobeniusMap.openPullback_eq_of_commute
  intro U s
  exact (SchemeFrobeniusMap.pushforward_app φ e.hom U s).symm

private theorem openPullback_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (fun φ : SchemeFrobeniusMap Y p => φ.openPullback e.hom) := by
  intro φ ψ h
  apply SchemeFrobeniusMap.ext
  intro U a
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective
  calc
    _ = (φ.openPullback e.hom).onOpen (e.hom ⁻¹ᵁ U) (e.hom.app U a) :=
      (SchemeFrobeniusMap.openPullback_natural φ e.hom U a).symm
    _ = (ψ.openPullback e.hom).onOpen (e.hom ⁻¹ᵁ U) (e.hom.app U a) :=
      congrArg (fun q => q.onOpen (e.hom ⁻¹ᵁ U) (e.hom.app U a)) h
    _ = _ := SchemeFrobeniusMap.openPullback_natural ψ e.hom U a

private theorem chart_openPullback {X Y : Scheme.{u}} (U : X.Opens)
    (e : Y ≅ U.toScheme) (φ : SchemeFrobeniusMap X p) (τ : SchemeFrobeniusMap Y p)
    (h : φ.restrict U = τ.pushforward e.hom) :
    φ.openPullback (e.hom ≫ U.ι) = τ := by
  have hrestrict := congrArg
    (fun ρ : SchemeFrobeniusMap U.toScheme p => ρ.openPullback e.hom)
    (SchemeFrobeniusMap.openPullback_restrict φ U)
  have hchart := congrArg
    (fun ρ : SchemeFrobeniusMap U.toScheme p => ρ.openPullback e.hom) h
  exact (SchemeFrobeniusMap.openPullback_comp φ e.hom U.ι).trans
    (hrestrict.trans (hchart.trans (pushforward_openPullback e τ)))


end SchubertGeometry.ProjectiveCartier
