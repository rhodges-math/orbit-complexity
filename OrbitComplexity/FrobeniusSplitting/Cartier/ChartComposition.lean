import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorCharts
import Batteries.Tactic.Lint

/-! # Composition and restriction of operator charts -/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace FrobeniusSplitting.SchemeFrobeniusMap

variable {X Y Z : Scheme.{u}} {p : ℕ}

/-- Open-chart transport composes along the underlying scheme morphisms. -/
theorem openPullback_comp (φ : SchemeFrobeniusMap Z p)
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    φ.openPullback (f ≫ g) = (φ.openPullback g).openPullback f := by
  apply openPullback_eq_of_commute
  intro U m
  change ((φ.openPullback g).openPullback f).onOpen (f ⁻¹ᵁ g ⁻¹ᵁ U)
      (f.app (g ⁻¹ᵁ U) (g.app U m)) =
    f.app (g ⁻¹ᵁ U) (g.app U (φ.onOpen U m))
  rw [(φ.openPullback g).openPullback_natural, φ.openPullback_natural]

/-- Transport by an open inclusion is the restriction of a sheaf operator. -/
theorem openPullback_restrict (φ : SchemeFrobeniusMap X p) (U : X.Opens) :
    φ.openPullback U.ι = φ.restrict U := by
  ext V m
  change (φ.onOpen (U.ι ''ᵁ V)).transport (U.ι.appIso V).commRingCatIsoToRingEquiv m =
    φ.onOpen (U.ι ''ᵁ V) m
  rw [U.ι_appIso]
  rfl

private theorem restriction_preimage (f : X ⟶ Y) (k : Z ⟶ Y)
    (U : X.Opens) (q : U.toScheme ⟶ Z) (h : U.ι ≫ f = q ≫ k)
    (V : Y.Opens) : U.ι ⁻¹ᵁ (f ⁻¹ᵁ V) = q ⁻¹ᵁ (k ⁻¹ᵁ V) :=
  congrArg (fun m : U.toScheme ⟶ Y => m ⁻¹ᵁ V) h

private theorem restriction_app (f : X ⟶ Y) (k : Z ⟶ Y)
    (U : X.Opens) (q : U.toScheme ⟶ Z) (h : U.ι ≫ f = q ≫ k)
    (V : Y.Opens) :
    k.app V ≫ q.app (k ⁻¹ᵁ V) =
      f.app V ≫ U.ι.app (f ⁻¹ᵁ V) ≫ U.toScheme.presheaf.map
        (eqToHom (restriction_preimage f k U q h V).symm).op := by
  have hc : k.app V ≫ q.app (k ⁻¹ᵁ V) =
      (f.app V ≫ U.ι.app (f ⁻¹ᵁ V)) ≫ U.toScheme.presheaf.map
        (eqToHom (restriction_preimage f k U q h V).symm).op := by
    simpa only [Scheme.Hom.comp_app, Scheme.Hom.comp_preimage] using
      Scheme.Hom.congr_app h.symm V
  exact hc.trans (Category.assoc _ _ _)

/-- Direct image of an operator commutes with restriction to an open chart
when both structure-sheaf maps are isomorphisms. -/
theorem openPullback_pushforward (φ : SchemeFrobeniusMap X p)
    (f : X ⟶ Y) [IsIso f.c] (k : Z ⟶ Y) [IsOpenImmersion k]
    (U : X.Opens) (q : U.toScheme ⟶ Z) [IsIso q.c]
    (h : U.ι ≫ f = q ≫ k) :
    (φ.pushforward f).openPullback k = (φ.restrict U).pushforward q := by
  apply openPullback_eq_of_commute
  intro V s
  apply (asIso (q.app (k ⁻¹ᵁ V))).commRingCatIsoToRingEquiv.injective
  change q.app (k ⁻¹ᵁ V)
      (((φ.restrict U).pushforward q).onOpen (k ⁻¹ᵁ V) (k.app V s)) =
    q.app (k ⁻¹ᵁ V) (k.app V ((φ.pushforward f).onOpen V s))
  rw [pushforward_app]
  let R := U.toScheme.presheaf.map
    (eqToHom (restriction_preimage f k U q h V).symm).op
  have hs (a : Γ(Y, V)) : q.app (k ⁻¹ᵁ V) (k.app V a) =
      R (U.ι.app (f ⁻¹ᵁ V) (f.app V a)) :=
    ConcreteCategory.congr_hom (restriction_app f k U q h V) a
  rw [hs s, hs ((φ.pushforward f).onOpen V s)]
  have ht := (φ.restrict U).restrict_comm
    (restriction_preimage f k U q h V).symm.le
    (U.ι.app (f ⁻¹ᵁ V) (f.app V s))
  have hmaps : (homOfLE (restriction_preimage f k U q h V).symm.le :
      (q ⁻¹ᵁ (k ⁻¹ᵁ V)) ⟶ (U.ι ⁻¹ᵁ (f ⁻¹ᵁ V))) =
      eqToHom (restriction_preimage f k U q h V).symm := Subsingleton.elim _ _
  rw [hmaps] at ht
  have hn := φ.openPullback_natural U.ι (f ⁻¹ᵁ V) (f.app V s)
  rw [openPullback_restrict] at hn
  exact ht.trans (congrArg R (hn.trans (congrArg (U.ι.app (f ⁻¹ᵁ V))
    (φ.pushforward_app f V s).symm)))

end FrobeniusSplitting.SchemeFrobeniusMap
