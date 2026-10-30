import OrbitComplexity.FrobeniusSplitting.Splittings.Gluing
import OrbitComplexity.FrobeniusSplitting.Splittings.Pushforward
import OrbitComplexity.FrobeniusSplitting.Splittings.Morphisms

/-! # Comparison of splitting formulas in open affine charts -/

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
variable {X S : Scheme.{u}} {p : ℕ}

private theorem chartFormula_app (U : X.Opens) (e : S ≅ U.toScheme)
    (splitting : SchemeSplitting S p) (V : X.Opens) (hV : V ≤ U) (s : Γ(X, V)) :
    (e.hom ≫ U.ι).app V
      (((splitting.pushforward e.hom).onSubopen V hV) s) =
        splitting.onOpen ((e.hom ≫ U.ι) ⁻¹ᵁ V) ((e.hom ≫ U.ι).app V s) := by
  change e.hom.app (U.ι ⁻¹ᵁ V) (U.ι.app V _) =
    splitting.onOpen (e.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V)
      (e.hom.app (U.ι ⁻¹ᵁ V) (U.ι.app V s))
  rw [onSubopen_app, pushforward_app]

private theorem chartFormula_natural {T : Scheme.{u}}
    (U : X.Opens) (e : S ≅ U.toScheme) (splitting : SchemeSplitting S p)
    (target : SchemeSplitting T p) (a : T ⟶ S)
    (ha : ∀ (W : S.Opens) (s : Γ(S, W)),
      target.onOpen (a ⁻¹ᵁ W) (a.app W s) = a.app W (splitting.onOpen W s))
    (V : X.Opens) (hV : V ≤ U) (s : Γ(X, V)) :
    (a ≫ e.hom ≫ U.ι).app V
      (((splitting.pushforward e.hom).onSubopen V hV) s) =
        target.onOpen ((a ≫ e.hom ≫ U.ι) ⁻¹ᵁ V)
          ((a ≫ e.hom ≫ U.ι).app V s) := by
  change a.app ((e.hom ≫ U.ι) ⁻¹ᵁ V)
    ((e.hom ≫ U.ι).app V _) = _
  rw [chartFormula_app, ← ha]
  rfl

/-- A common open chart compares transported splittings when its ring maps commute with them. -/
theorem chartFormula_eq {T S' : Scheme.{u}}
    (U U' : X.Opens) (e : S ≅ U.toScheme) (e' : S' ≅ U'.toScheme)
    (splitting : SchemeSplitting S p) (other : SchemeSplitting S' p)
    (target : SchemeSplitting T p) (a : T ⟶ S) (b : T ⟶ S')
    (ha : ∀ (W : S.Opens) (s : Γ(S, W)),
      target.onOpen (a ⁻¹ᵁ W) (a.app W s) = a.app W (splitting.onOpen W s))
    (hb : ∀ (W : S'.Opens) (s : Γ(S', W)),
      target.onOpen (b ⁻¹ᵁ W) (b.app W s) = b.app W (other.onOpen W s))
    (hab : a ≫ e.hom ≫ U.ι = b ≫ e'.hom ≫ U'.ι)
    [IsOpenImmersion (a ≫ e.hom ≫ U.ι)]
    (V : X.Opens) (hV : V ≤ U) (hV' : V ≤ U')
    (himage : V ≤ (a ≫ e.hom ≫ U.ι).opensRange) :
    (splitting.pushforward e.hom).onSubopen V hV =
      (other.pushforward e'.hom).onSubopen V hV' := by
  have : IsIso ((a ≫ e.hom ≫ U.ι).app V) :=
    (a ≫ e.hom ≫ U.ι).isIso_app V himage
  ext s
  apply (asIso ((a ≫ e.hom ≫ U.ι).app V)).commRingCatIsoToRingEquiv.injective
  change (a ≫ e.hom ≫ U.ι).app V _ = (a ≫ e.hom ≫ U.ι).app V _
  rw [chartFormula_natural U e splitting target a ha]
  rw [hab, chartFormula_natural U' e' other target b hb]

end
end FrobeniusSplitting.SchemeSplitting
