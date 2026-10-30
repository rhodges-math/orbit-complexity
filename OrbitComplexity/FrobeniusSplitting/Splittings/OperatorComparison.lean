import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorGluing
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorMorphisms

/-! # Transport of sheaf operators to open charts -/

namespace FrobeniusSplitting.SchemeFrobeniusMap

open AlgebraicGeometry CategoryTheory Opposite

variable {X Y : Scheme} {p : ℕ}

/-- An operator descends when the structure sheaf map to the direct image is an isomorphism. -/
noncomputable def pushforward (splitting : SchemeFrobeniusMap X p) (morphism : X ⟶ Y)
    [IsIso morphism.c] : SchemeFrobeniusMap Y p where
  onOpen U := (splitting.onOpen (morphism ⁻¹ᵁ U)).transport
    (asIso (morphism.app U)).symm.commRingCatIsoToRingEquiv
  restrict_comm {U V} h s := by
    have heval (W : Y.Opens) (a : Γ(Y, W)) :
        morphism.app W
          ((splitting.onOpen (morphism ⁻¹ᵁ W)).transport
            (asIso (morphism.app W)).symm.commRingCatIsoToRingEquiv a) =
        splitting.onOpen (morphism ⁻¹ᵁ W) (morphism.app W a) := by
      exact (asIso (morphism.app W)).commRingCatIsoToRingEquiv.apply_symm_apply _
    have hpreimage : morphism ⁻¹ᵁ V ≤ morphism ⁻¹ᵁ U := fun _ hx ↦ h hx
    have hnaturality (a : Γ(Y, U)) :
        morphism.app V (Y.presheaf.map (homOfLE h).op a) =
          X.presheaf.map (homOfLE hpreimage).op (morphism.app U a) := by
      exact congrArg (fun f : Γ(Y, U) ⟶ Γ(X, morphism ⁻¹ᵁ V) ↦ f a)
        (morphism.naturality (homOfLE h).op)
    apply (asIso (morphism.app V)).commRingCatIsoToRingEquiv.injective
    change morphism.app V _ = morphism.app V _
    rw [heval, hnaturality, splitting.restrict_comm hpreimage]
    rw [hnaturality, heval]

/-- Pulling back a descended operator agrees with splitting the pulled back section. -/
theorem pushforward_app (splitting : SchemeFrobeniusMap X p) (morphism : X ⟶ Y)
    [IsIso morphism.c] (U : Y.Opens) (s : Γ(Y, U)) :
    morphism.app U ((splitting.pushforward morphism).onOpen U s) =
      splitting.onOpen (morphism ⁻¹ᵁ U) (morphism.app U s) :=
  (asIso (morphism.app U)).commRingCatIsoToRingEquiv.apply_symm_apply _

end FrobeniusSplitting.SchemeFrobeniusMap

namespace FrobeniusSplitting.SchemeFrobeniusMap

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
variable {X S : Scheme.{u}} {p : ℕ}

private theorem chartFormula_app (U : X.Opens) (e : S ≅ U.toScheme)
    (splitting : SchemeFrobeniusMap S p) (V : X.Opens) (hV : V ≤ U) (s : Γ(X, V)) :
    (e.hom ≫ U.ι).app V
      (((splitting.pushforward e.hom).onSubopen V hV) s) =
        splitting.onOpen ((e.hom ≫ U.ι) ⁻¹ᵁ V) ((e.hom ≫ U.ι).app V s) := by
  change e.hom.app (U.ι ⁻¹ᵁ V) (U.ι.app V _) =
    splitting.onOpen (e.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V)
      (e.hom.app (U.ι ⁻¹ᵁ V) (U.ι.app V s))
  rw [onSubopen_app, pushforward_app]

private theorem chartFormula_natural {T : Scheme.{u}}
    (U : X.Opens) (e : S ≅ U.toScheme) (splitting : SchemeFrobeniusMap S p)
    (target : SchemeFrobeniusMap T p) (a : T ⟶ S)
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

/-- A common open chart compares transported operators when its ring maps commute with them. -/
theorem chartFormula_eq {T S' : Scheme.{u}}
    (U U' : X.Opens) (e : S ≅ U.toScheme) (e' : S' ≅ U'.toScheme)
    (splitting : SchemeFrobeniusMap S p) (other : SchemeFrobeniusMap S' p)
    (target : SchemeFrobeniusMap T p) (a : T ⟶ S) (b : T ⟶ S')
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
end FrobeniusSplitting.SchemeFrobeniusMap
