import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Frobenius scalars for sheaves of modules -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace FrobeniusSplitting
universe u

private def coefficients (C : Type u) [CommRing C] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (U : X.Opens) : C →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of C)).inv ≫ (U.ι ≫ base).appTop ≫ U.topIso.hom).hom

private theorem section_add_pow (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) (a b : Γ(X, U)) :
    (a + b) ^ p = a ^ p + b ^ p := by
  rcases expChar_is_prime_or_one C p with hp | rfl
  · let : CharP C p := (expChar_prime_iff C hp).mp inferInstance
    have hC : (p : C) = 0 := CharP.cast_eq_zero C p
    have hU : (p : Γ(X, U)) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (coefficients C base U) hC
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
    simpa [hU] using hr
  · simp

private def sectionPower (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) :
    Γ(X, U) →+* Γ(X, U) where
  toFun a := a ^ p
  map_zero' := zero_pow (expChar_ne_zero C p)
  map_one' := one_pow p
  map_add' := section_add_pow C p base U
  map_mul' := fun _ _ => mul_pow _ _ _

/-- The absolute-Frobenius endomorphism of the ring sheaf, including the empty open. -/
def sheafFrobenius (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) : X.ringCatSheaf ⟶ X.ringCatSheaf where
  hom.app U := RingCat.ofHom (sectionPower C p base U.unop)
  hom.naturality {U V} f := by
    ext a
    change (X.presheaf.map f a) ^ p = X.presheaf.map f (a ^ p)
    exact ((X.presheaf.map f).hom.map_pow a p).symm

/-- Scalar restriction along the absolute Frobenius retains the underlying module sheaf. -/
def frobeniusRestriction (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M : X.Modules) : X.Modules :=
  (SheafOfModules.pushforward (F := 𝟭 X.Opens) (sheafFrobenius C p base)).obj M

/-- In the restricted module sheaf, a section acts by its pth power. -/
example (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : (M.val.obj (.op U))) :
    ((frobeniusRestriction C p base M).smul r).hom s = (M.smul (r ^ p)).hom s := rfl

private def powerHom (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c.app U := CommRingCat.ofHom ((sheafFrobenius C p base).hom.app U).hom
  c.naturality {U V} f := by
    ext a
    change (X.presheaf.map f a) ^ p = X.presheaf.map f (a ^ p)
    exact ((X.presheaf.map f).hom.map_pow a p).symm

private theorem powerHom_stalk (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (x : X)
    (a : X.presheaf.stalk x) :
    (powerHom C p base).stalkMap x a = a ^ p := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  erw [PresheafedSpace.stalkMap_germ_apply]
  change X.presheaf.germ U x hx (s ^ p) = (X.presheaf.germ U x hx s) ^ p
  exact (X.presheaf.germ U x hx).hom.map_pow s p

/-- Absolute Frobenius is a scheme morphism with identity underlying map. -/
def schemeFrobenius (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) : X ⟶ X where
  toLRSHom' :=
    { toHom := powerHom C p base
      prop x :=
        { map_nonunit := fun a ha => by
            rw [show (powerHom C p base).stalkMap x a = a ^ p from
              powerHom_stalk C p base x a] at ha
            exact (isUnit_pow_iff (expChar_ne_zero C p)).mp ha } }

/-- On every open, the scheme morphism acts by the pth power on sections. -/
example (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) (s : Γ(X, U)) :
    (schemeFrobenius C p base).app U s = s ^ p := rfl

/-- On an affine scheme, Frobenius scalar restriction preserves quasicoherence. -/
theorem frobeniusAffine_isQuasicoherent (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {R : CommRingCat.{u}} (base : Spec R ⟶ Spec (.of C)) (M : (Spec R).Modules)
    [M.IsQuasicoherent] : (frobeniusRestriction C p base M).IsQuasicoherent := by
  have he : frobeniusRestriction C p base M =
      (Scheme.Modules.pushforward (schemeFrobenius C p base)).obj M := rfl
  rw [he]
  have h := isIso_fromTildeΓ_pushforward
    (Spec.preimage (schemeFrobenius C p base)) M
  have hq := (isQuasicoherent_iff_isIso_fromTildeΓ
    ((Scheme.Modules.pushforward (Spec.map (Spec.preimage
      (schemeFrobenius C p base)))).obj M)).mpr h
  simpa only [Spec.map_preimage] using hq

/-- Open restriction commutes with the absolute-Frobenius scalar restriction. -/
def frobeniusRestrictIso (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X Y : Scheme.{u}} (base : Y ⟶ Spec (.of C)) (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) :
    (frobeniusRestriction C p base M).restrict f ≅
      frobeniusRestriction C p (f ≫ base) (M.restrict f) := by
  refine (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).preimageIso
    (PresheafOfModules.isoMk (fun U => ?_) ?_)
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    change (M.smul ((f.appIso U.unop).inv (r ^ p))).hom m =
      (M.smul (((f.appIso U.unop).inv r) ^ p)).hom m
    erw [(f.appIso U.unop).inv.hom.map_pow]
  · intro U V g
    ext m
    rfl

end FrobeniusSplitting
