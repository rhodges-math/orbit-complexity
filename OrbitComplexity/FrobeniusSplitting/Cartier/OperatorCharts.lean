import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorComparison

/-! # Weights and open-chart transport of sheaf operators -/

namespace FrobeniusSplitting.SchemeFrobeniusMap

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
variable {X Y : Scheme.{u}} {p : ℕ}

/-- A global section weights the input of an operator on each open subset. -/
def inputWeight (φ : SchemeFrobeniusMap X p) (r : Γ(X, ⊤)) :
    SchemeFrobeniusMap X p where
  onOpen U := (φ.onOpen U).weight (X.presheaf.map U.leTop.op r)
  restrict_comm {U V} h s := by
    have ht : X.presheaf.map (homOfLE h).op
        (X.presheaf.map U.leTop.op r) = X.presheaf.map V.leTop.op r := by
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl
    change φ.onOpen V (X.presheaf.map V.leTop.op r *
      X.presheaf.map (homOfLE h).op s) =
        X.presheaf.map (homOfLE h).op
          (φ.onOpen U (X.presheaf.map U.leTop.op r * s))
    rw [← φ.restrict_comm h, (X.presheaf.map (homOfLE h).op).hom.map_mul, ht]

/-- The weighted operator applies the original operator after input multiplication. -/
theorem inputWeight_apply (φ : SchemeFrobeniusMap X p) (r : Γ(X, ⊤))
    (U : X.Opens) (m : Γ(X, U)) :
    (φ.inputWeight r).onOpen U m =
      φ.onOpen U (X.presheaf.map U.leTop.op r * m) := rfl

private def openComponent (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) : FrobeniusLinearMap Γ(X, U) p :=
  (φ.onOpen (f ''ᵁ U)).transport (f.appIso U).commRingCatIsoToRingEquiv

private theorem openComponent_inv (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (m : Γ(X, U)) :
    (f.appIso U).inv (openComponent φ f U m) =
      φ.onOpen (f ''ᵁ U) ((f.appIso U).inv m) :=
  (f.appIso U).commRingCatIsoToRingEquiv.symm_apply_apply _

/-- Open immersion charts transport operators on every ring of sections. -/
def openPullback (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y) [IsOpenImmersion f] :
    SchemeFrobeniusMap X p where
  onOpen U := openComponent φ f U
  restrict_comm {U V} h m := by
    have hnat (a : Γ(X, U)) :
        (f.appIso V).inv (X.presheaf.map (homOfLE h).op a) =
          Y.presheaf.map (homOfLE (f.image_mono h)).op ((f.appIso U).inv a) :=
      congrArg (fun k : Γ(X, U) ⟶ Γ(Y, f ''ᵁ V) => k a)
        (f.appIso_inv_naturality (homOfLE h).op)
    apply (f.appIso V).commRingCatIsoToRingEquiv.symm.injective
    change (f.appIso V).inv (openComponent φ f V
        (X.presheaf.map (homOfLE h).op m)) =
      (f.appIso V).inv (X.presheaf.map (homOfLE h).op (openComponent φ f U m))
    rw [openComponent_inv, hnat, φ.restrict_comm (f.image_mono h), hnat,
      openComponent_inv]

/-- The chart's section isomorphism conjugates the transported operator. -/
theorem openPullback_appIso (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (m : Γ(X, U)) :
    (f.appIso U).inv ((φ.openPullback f).onOpen U m) =
      φ.onOpen (f ''ᵁ U) ((f.appIso U).inv m) := openComponent_inv φ f U m

/-- Naturality for the structure-sheaf maps identifies an open-chart operator. -/
theorem openPullback_eq_of_commute (φ : SchemeFrobeniusMap Y p)
    (ψ : SchemeFrobeniusMap X p) (f : X ⟶ Y) [IsOpenImmersion f]
    (h : ∀ (U : Y.Opens) (m : Γ(Y, U)),
      ψ.onOpen (f ⁻¹ᵁ U) (f.app U m) = f.app U (φ.onOpen U m)) :
    φ.openPullback f = ψ := by
  ext U r
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  obtain ⟨m, rfl⟩ := e.surjective r
  have hcompat : ψ.onOpen U ((f.appIso U).hom m) =
      (f.appIso U).hom (φ.onOpen (f ''ᵁ U) m) := by
    have hr := ψ.restrict_comm (f.preimage_image_eq U).symm.le (f.app (f ''ᵁ U) m)
    have hn := congrArg
      (fun a : Γ(X, f ⁻¹ᵁ f ''ᵁ U) =>
        X.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op a)
      (h (f ''ᵁ U) m)
    rw [f.appIso_hom]
    change ψ.onOpen U
        (X.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op
          (f.app (f ''ᵁ U) m)) =
      X.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op
        (f.app (f ''ᵁ U) (φ.onOpen (f ''ᵁ U) m))
    exact hr.trans hn
  change (φ.onOpen (f ''ᵁ U)).transport e (e m) = ψ.onOpen U (e m)
  rw [FrobeniusLinearMap.transport_apply, e.symm_apply_apply]
  exact hcompat.symm

/-- Pullback along an open chart commutes with its structure-sheaf maps. -/
theorem openPullback_natural (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : Y.Opens) (m : Γ(Y, U)) :
    (φ.openPullback f).onOpen (f ⁻¹ᵁ U) (f.app U m) =
      f.app U (φ.onOpen U m) := by
  have heval (a : Γ(Y, U)) :
      (f.appIso (f ⁻¹ᵁ U)).inv (f.app U a) =
        Y.presheaf.map (homOfLE (f.image_preimage_le U)).op a :=
    congrArg (fun k : Γ(Y, U) ⟶ Γ(Y, f ''ᵁ f ⁻¹ᵁ U) => k a)
      (f.app_appIso_inv U)
  apply (f.appIso (f ⁻¹ᵁ U)).commRingCatIsoToRingEquiv.symm.injective
  change (f.appIso (f ⁻¹ᵁ U)).inv
      ((φ.openPullback f).onOpen (f ⁻¹ᵁ U) (f.app U m)) =
    (f.appIso (f ⁻¹ᵁ U)).inv (f.app U (φ.onOpen U m))
  rw [openPullback_appIso, heval, φ.restrict_comm (f.image_preimage_le U), heval]

/-- Open-chart transport carries input weights by the global structure-sheaf map. -/
theorem openPullback_inputWeight (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y)
    [IsOpenImmersion f] (r : Γ(Y, ⊤)) :
    (φ.inputWeight r).openPullback f =
      (φ.openPullback f).inputWeight (f.appTop r) := by
  apply openPullback_eq_of_commute
  intro U m
  have hr : X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r) =
      f.app U (Y.presheaf.map U.leTop.op r) :=
    (congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) => k r)
      (f.naturality U.leTop.op)).symm
  change (φ.openPullback f).onOpen (f ⁻¹ᵁ U)
      (X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r) * f.app U m) =
    f.app U (φ.onOpen U (Y.presheaf.map U.leTop.op r * m))
  rw [hr, ← (f.app U).hom.map_mul]
  exact φ.openPullback_natural f U (Y.presheaf.map U.leTop.op r * m)

/-- Scheme isomorphisms identify all Frobenius-linear sheaf operators. -/
def operatorIsoEquiv (e : X ≅ Y) : SchemeFrobeniusMap X p ≃ SchemeFrobeniusMap Y p where
  toFun φ := φ.pushforward e.hom
  invFun ψ := ψ.openPullback e.hom
  left_inv φ :=
    openPullback_eq_of_commute (φ.pushforward e.hom) φ e.hom
      (fun U m => (φ.pushforward_app e.hom U m).symm)
  right_inv ψ := by
    ext U m
    apply (asIso (e.hom.app U)).commRingCatIsoToRingEquiv.injective
    exact ((ψ.openPullback e.hom).pushforward_app e.hom U m).trans
      (ψ.openPullback_natural e.hom U m)

end

end FrobeniusSplitting.SchemeFrobeniusMap
