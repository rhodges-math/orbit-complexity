import OrbitComplexity.FrobeniusSplitting.Splittings.AffineExt
import OrbitComplexity.FrobeniusSplitting.Splittings.Spec
import OrbitComplexity.FrobeniusSplitting.Splittings.Morphisms
import Batteries.Tactic.Lint

/-! # Splittings and affine coordinates

The splitting constructed from an affine scheme's coordinate ring has the
prescribed action on global sections. Thus the construction recovers every
splitting on an affine scheme.
-/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u
namespace FrobeniusSplitting

private theorem affine_inverse_map {X : Scheme.{u}} [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have hi : Scheme.Γ.mapIso X.isoSpec.op = Scheme.ΓSpecIso Γ(X, ⊤) :=
    Iso.ext (X.toSpecΓ_appTop)
  exact congrArg Iso.inv hi

namespace RingSplitting

/-- The affine splitting acts on global sections by the original ring splitting. -/
theorem toAffine_top {X : Scheme.{u}} [IsAffine X] {p : ℕ}
    (base : RingSplitting Γ(X, ⊤) p) (hp : 0 < p) (a : Γ(X, ⊤)) :
    (base.toAffine hp).onOpen ⊤ a = base a := by
  have : IsIso X.isoSpec.inv.c :=
    PresheafedSpace.c_isIso_of_iso X.isoSpec.inv.toPshHom
  have h := (base.toSpec hp).pushforward_app X.isoSpec.inv ⊤ a
  change X.isoSpec.inv.appTop ((base.toAffine hp).onOpen ⊤ a) =
    (base.toSpec hp).onOpen ⊤ (X.isoSpec.inv.appTop a) at h
  rw [affine_inverse_map] at h
  apply (Scheme.ΓSpecIso Γ(X, ⊤)).symm.commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso Γ(X, ⊤)).inv ((base.toAffine hp).onOpen ⊤ a) =
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv (base a)
  apply h.trans
  change (base.toSpec hp).onOpen ⊤ (StructureSheaf.toOpenₗ Γ(X, ⊤) Γ(X, ⊤) ⊤ a) =
    StructureSheaf.toOpenₗ Γ(X, ⊤) Γ(X, ⊤) ⊤ (base a)
  exact base.toSpec_constant hp ⊤ a

end RingSplitting
namespace SchemeSplitting

/-- Passing to the global coordinate ring and back recovers an affine splitting. -/
theorem eq_toAffine {X : Scheme.{u}} [IsAffine X] {p : ℕ}
    (splitting : SchemeSplitting X p) (hp : 0 < p) :
    splitting = (splitting.onOpen ⊤).toAffine hp := by
  apply eq_of_top _ _ hp
  apply RingSplitting.ext
  intro a
  exact (RingSplitting.toAffine_top (splitting.onOpen ⊤) hp a).symm

private theorem app_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    f.app V (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op
        (f.app U a) :=
  congrArg (fun t : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ V) => t a)
    (f.naturality (homOfLE h).op)

private theorem natural_basic {X Y : Scheme.{u}} [IsAffine Y] {p : ℕ}
    (source : SchemeSplitting X p) (target : SchemeSplitting Y p)
    (f : X ⟶ Y) (hp : 0 < p)
    (h : ∀ a, source.onOpen ⊤ (f.appTop a) = f.appTop (target.onOpen ⊤ a))
    (r : Γ(Y, ⊤)) (s : Γ(Y, Y.basicOpen r)) :
    source.onOpen (f ⁻¹ᵁ Y.basicOpen r) (f.app (Y.basicOpen r) s) =
      f.app (Y.basicOpen r) (target.onOpen (Y.basicOpen r) s) := by
  have hc : ∀ a : Γ(Y, ⊤),
      source.onOpen (f ⁻¹ᵁ Y.basicOpen r)
        (f.app (Y.basicOpen r) (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r) a)) =
      f.app (Y.basicOpen r)
        (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r) (target.onOpen ⊤ a)) := by
    intro a
    change source.onOpen (f ⁻¹ᵁ Y.basicOpen r)
        (f.app (Y.basicOpen r) (Y.presheaf.map (homOfLE le_top).op a)) =
      f.app (Y.basicOpen r)
        (Y.presheaf.map (homOfLE le_top).op (target.onOpen ⊤ a))
    have hr (z : Γ(Y, ⊤)) :
        f.app (Y.basicOpen r) (Y.presheaf.map (homOfLE le_top).op z) =
          X.presheaf.map (homOfLE le_top).op (f.appTop z) := by
      erw [app_restrict]
      rfl
    calc
      _ = source.onOpen (f ⁻¹ᵁ Y.basicOpen r)
          (X.presheaf.map (homOfLE le_top).op (f.appTop a)) :=
        congrArg (source.onOpen (f ⁻¹ᵁ Y.basicOpen r)) (hr a)
      _ = X.presheaf.map (homOfLE le_top).op (source.onOpen ⊤ (f.appTop a)) :=
        source.restrict_comm le_top (f.appTop a)
      _ = X.presheaf.map (homOfLE le_top).op (f.appTop (target.onOpen ⊤ a)) :=
        congrArg (fun z : Γ(X, ⊤) => X.presheaf.map (homOfLE le_top).op z) (h a)
      _ = _ := (hr (target.onOpen ⊤ a)).symm
  have hn := RingSplitting.map_localize (Submonoid.powers r)
    (target.onOpen ⊤) hp (source.onOpen (f ⁻¹ᵁ Y.basicOpen r))
    (f.app (Y.basicOpen r)).hom hc s
  have hl := RingSplitting.localize_eq (S := Γ(Y, Y.basicOpen r)) (Submonoid.powers r)
    (target.onOpen ⊤) hp (target.onOpen (Y.basicOpen r))
    (fun a => target.restrict_comm le_top a)
  exact hn.trans (congrArg (fun t : RingSplitting Γ(Y, Y.basicOpen r) p =>
    f.app (Y.basicOpen r) (t s)) hl)

/-- A morphism to an affine scheme commutes with splittings if its map on
 global sections does so. -/
theorem natural_of_top {X Y : Scheme.{u}} [IsAffine Y] {p : ℕ}
    (source : SchemeSplitting X p) (target : SchemeSplitting Y p)
    (f : X ⟶ Y) (hp : 0 < p)
    (h : ∀ a, source.onOpen ⊤ (f.appTop a) = f.appTop (target.onOpen ⊤ a))
    (U : Y.Opens) (s : Γ(Y, U)) :
    source.onOpen (f ⁻¹ᵁ U) (f.app U s) = f.app U (target.onOpen U s) := by
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨f x, hx⟩ (by trivial)
  let W := f ⁻¹ᵁ Y.basicOpen r
  have hW : W ≤ f ⁻¹ᵁ U := fun _ hx => hr hx
  refine ⟨W, hW, hxr, ?_⟩
  calc
    _ = source.onOpen W
        (X.presheaf.map (homOfLE hW).op (f.app U s)) :=
      (source.restrict_comm hW (f.app U s)).symm
    _ = source.onOpen W
        (f.app (Y.basicOpen r) (Y.presheaf.map (homOfLE hr).op s)) :=
      congrArg (source.onOpen W) (app_restrict f hr s).symm
    _ = f.app (Y.basicOpen r)
        (target.onOpen (Y.basicOpen r) (Y.presheaf.map (homOfLE hr).op s)) :=
      natural_basic source target f hp h r _
    _ = f.app (Y.basicOpen r)
        (Y.presheaf.map (homOfLE hr).op (target.onOpen U s)) :=
      congrArg (f.app (Y.basicOpen r)) (target.restrict_comm hr s)
    _ = _ := app_restrict f hr (target.onOpen U s)

end SchemeSplitting
end FrobeniusSplitting
