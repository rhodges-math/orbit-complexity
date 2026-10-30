import OrbitComplexity.FrobeniusSplitting.Compatible.ClosedCover
import OrbitComplexity.FrobeniusSplitting.Compatible.Local
import OrbitComplexity.FrobeniusSplitting.Compatible.ClosedQuotient
import OrbitComplexity.FrobeniusSplitting.Splittings.AffineMorphisms
import Batteries.Tactic.Lint

/-! # Closed subschemes split on an affine ambient cover

Compatible quotients on an affine ambient cover inherit their projection
formulas from the ambient splitting. These formulas determine agreement on
overlaps and give a splitting of the same closed subscheme.
-/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u
namespace FrobeniusSplitting.SchemeSplitting

private theorem closed_affine_natural {X Y : Scheme.{u}} [IsAffine X] {p : ℕ}
    (ambient : SchemeSplitting X p) (j : Y ⟶ X) [IsClosedImmersion j]
    (hp : 0 < p) (hker : ambient.IsCompatible j.ker)
    (V : X.Opens) (a : Γ(X, V)) :
    (ambient.closedAffine j hp hker).onOpen (j ⁻¹ᵁ V) (j.app V a) =
      j.app V (ambient.onOpen V a) := by
  apply natural_of_top _ ambient j hp _ V a
  intro b
  let : IsAffine Y := isAffine_of_isAffineHom j
  unfold closedAffine
  rw [RingSplitting.toAffine_top]
  erw [RingSplitting.ofSurjective_map]

private theorem restriction_open {X Y : Scheme.{u}} (j : Y ⟶ X)
    (U V : X.Opens) :
    (j ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V) = (j ⁻¹ᵁ U).ι ⁻¹ᵁ (j ⁻¹ᵁ V) := by
  simpa only [Scheme.Hom.comp_preimage] using
    congrArg (fun t : (j ⁻¹ᵁ U).toScheme ⟶ X => t ⁻¹ᵁ V) (morphismRestrict_ι j U)

private theorem cancel_eq_map {A D : Type*} [Category A] [Category D]
    (F : Aᵒᵖ ⥤ D) {U V : A} (h : U = V) {Z : D}
    (a : Z ⟶ F.obj (op U)) (b : Z ⟶ F.obj (op V))
    (ha : a = b ≫ F.map (eqToHom h).op) :
    a ≫ F.map (eqToHom h.symm).op = b := by
  cases h
  have hF : F.map (𝟙 (op U)) = 𝟙 (F.obj (op U)) :=
    CategoryTheory.Functor.map_id F (op U)
  simpa only [eqToHom_refl, op_id, hF, Category.comp_id] using ha

private theorem restriction_square {X Y : Scheme.{u}} (j : Y ⟶ X)
    (U V : X.Opens) :
    U.ι.app V ≫ (j ∣_ U).app (U.ι ⁻¹ᵁ V) ≫
        (j ⁻¹ᵁ U).toScheme.presheaf.map
          (eqToHom (restriction_open j U V).symm).op =
      j.app V ≫ (j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V) := by
  have h : U.ι.app V ≫ (j ∣_ U).app (U.ι ⁻¹ᵁ V) =
      (j.app V ≫ (j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V)) ≫
        (j ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (restriction_open j U V)).op := by
    simpa only [Scheme.Hom.comp_app, Scheme.Hom.comp_preimage, Category.assoc] using
      Scheme.Hom.congr_app (morphismRestrict_ι j U) V
  simpa only [Category.assoc] using cancel_eq_map
    (j ⁻¹ᵁ U).toScheme.presheaf (restriction_open j U V)
    (U.ι.app V ≫ (j ∣_ U).app (U.ι ⁻¹ᵁ V))
    (j.app V ≫ (j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V)) h

private theorem split_eq_transport {X : Scheme.{u}} {p : ℕ}
    (splitting : SchemeSplitting X p) {U V : X.Opens} (h : U = V) (a : Γ(X, U)) :
    splitting.onOpen V (X.presheaf.map (eqToHom h.symm).op a) =
      X.presheaf.map (eqToHom h.symm).op (splitting.onOpen U a) :=
  splitting.restrict_comm h.symm.le a

private theorem restriction_natural {X Y : Scheme.{u}} {p : ℕ}
    (j : Y ⟶ X) (ambient : SchemeSplitting X p) (U : X.Opens)
    (localSplitting : SchemeSplitting (j ⁻¹ᵁ U).toScheme p)
    (hlocal : ∀ (W : U.toScheme.Opens) (a : Γ(U.toScheme, W)),
      localSplitting.onOpen ((j ∣_ U) ⁻¹ᵁ W) ((j ∣_ U).app W a) =
        (j ∣_ U).app W ((ambient.restrict U).onOpen W a))
    (V : X.Opens) (hV : V ≤ U) (a : Γ(X, V)) :
    localSplitting.onSubopen (j ⁻¹ᵁ V) (fun _ hx => hV hx) (j.app V a) =
      j.app V (ambient.onOpen V a) := by
  have hW : j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U := fun _ hx => hV hx
  have : IsIso ((j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V)) :=
    (j ⁻¹ᵁ U).ι.isIso_app (j ⁻¹ᵁ V) (by simpa using hW)
  let δ := (j ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (restriction_open j U V).symm).op
  have hs (b : Γ(X, V)) :
      δ ((j ∣_ U).app (U.ι ⁻¹ᵁ V) (U.ι.app V b)) =
        (j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V) (j.app V b) :=
    congrArg (fun t : Γ(X, V) ⟶
      Γ((j ⁻¹ᵁ U).toScheme, (j ⁻¹ᵁ U).ι ⁻¹ᵁ (j ⁻¹ᵁ V)) => t b)
        (restriction_square j U V)
  have hsource :
      (ambient.restrict U).onOpen (U.ι ⁻¹ᵁ V) (U.ι.app V a) =
        U.ι.app V (ambient.onOpen V a) := by
    have h := (ambient.restrict U).onSubopen_app V hV a
    rw [restrict_onSubopen] at h
    exact h.symm
  apply (asIso ((j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V))).commRingCatIsoToRingEquiv.injective
  change (j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V)
      (localSplitting.onSubopen (j ⁻¹ᵁ V) (fun _ hx => hV hx) (j.app V a)) =
    (j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V) (j.app V (ambient.onOpen V a))
  calc
    _ = localSplitting.onOpen ((j ⁻¹ᵁ U).ι ⁻¹ᵁ (j ⁻¹ᵁ V))
        ((j ⁻¹ᵁ U).ι.app (j ⁻¹ᵁ V) (j.app V a)) :=
      localSplitting.onSubopen_app (j ⁻¹ᵁ V) hW (j.app V a)
    _ = localSplitting.onOpen ((j ⁻¹ᵁ U).ι ⁻¹ᵁ (j ⁻¹ᵁ V))
        (δ ((j ∣_ U).app (U.ι ⁻¹ᵁ V) (U.ι.app V a))) :=
      congrArg (localSplitting.onOpen ((j ⁻¹ᵁ U).ι ⁻¹ᵁ (j ⁻¹ᵁ V))) (hs a).symm
    _ = δ (localSplitting.onOpen ((j ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V))
        ((j ∣_ U).app (U.ι ⁻¹ᵁ V) (U.ι.app V a))) :=
      split_eq_transport localSplitting (restriction_open j U V) _
    _ = δ ((j ∣_ U).app (U.ι ⁻¹ᵁ V)
        ((ambient.restrict U).onOpen (U.ι ⁻¹ᵁ V) (U.ι.app V a))) :=
      congrArg δ (hlocal (U.ι ⁻¹ᵁ V) (U.ι.app V a))
    _ = δ ((j ∣_ U).app (U.ι ⁻¹ᵁ V) (U.ι.app V (ambient.onOpen V a))) :=
      congrArg (fun t : Γ(U.toScheme, U.ι ⁻¹ᵁ V) => δ ((j ∣_ U).app (U.ι ⁻¹ᵁ V) t)) hsource
    _ = _ := hs (ambient.onOpen V a)

/-- A closed subscheme is split when its ideal is compatible on an affine
ambient cover under one fixed splitting. -/
def closedOfCover {X Y : Scheme.{u}} {p : ℕ}
    (ambient : SchemeSplitting X p) (j : Y ⟶ X) [IsClosedImmersion j]
    (hp : 0 < p) {I : Type u} (U : I → X.Opens)
    (hcover : ⨆ i, U i = ⊤) (hU : ∀ i, IsAffineOpen (U i))
    (hker : ∀ i, (ambient.restrict (U i)).IsCompatible (j ∣_ U i).ker) :
    SchemeSplitting Y p :=
  glueClosedCover j ambient U hcover
    (fun i => by
      letI : IsAffine (U i).toScheme := hU i
      exact (ambient.restrict (U i)).closedAffine (j ∣_ U i) hp (hker i))
    (fun i V hV a => by
      let : IsAffine (U i).toScheme := hU i
      exact restriction_natural j ambient (U i)
        ((ambient.restrict (U i)).closedAffine (j ∣_ U i) hp (hker i))
        (closed_affine_natural (ambient.restrict (U i)) (j ∣_ U i) hp (hker i)) V hV a)

private theorem compatible_kernel {X Y : Scheme.{u}} [IsAffine X] {p : ℕ}
    (ambient : SchemeSplitting X p) (j : Y ⟶ X) [IsClosedImmersion j]
    (hp : 0 < p)
    (h : (ambient.onOpen ⊤).IsCompatible (RingHom.ker j.appTop.hom)) :
    ambient.IsCompatible j.ker := by
  apply isCompatible_of_cover ambient j.ker hp
    (fun _ : Fin 1 => ⟨⊤, isAffineOpen_top X⟩) (by simp)
  intro k
  erw [j.ker_apply ⟨⊤, isAffineOpen_top X⟩]
  exact h

/-- A closed subscheme whose kernel is compatible with an ambient splitting inherits
that splitting. -/
def closedOfCompatible {X Y : Scheme.{u}} {p : ℕ}
    (ambient : SchemeSplitting X p) (j : Y ⟶ X) [jClosed : IsClosedImmersion j]
    (hp : 0 < p) (hker : ambient.IsCompatible j.ker) : SchemeSplitting Y p := by
  refine @closedOfCover.{u} X Y p ambient j jClosed hp X.affineOpens
    (fun U => U.1) (iSup_affineOpens_eq_top X) (fun U => U.2) ?_
  intro U V
  change (ambient.onOpen (U.1.ι ''ᵁ V.1)).IsCompatible ((j ∣_ U.1).ker.ideal V)
  rw [Scheme.ker_morphismRestrict_ideal]
  exact hker ⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩

end FrobeniusSplitting.SchemeSplitting
