import OrbitComplexity.FrobeniusSplitting.Splittings.Localization
import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import OrbitComplexity.FrobeniusSplitting.Splittings.Pushforward

/-!
# Splittings of affine spectra

A ring splitting extends to local fractions with the same denominator after multiplying
its numerator by the denominator to the power `p - 1`. These local formulas define
splittings on every open subset of the spectrum, and hence on affine schemes.
-/

namespace FrobeniusSplitting.RingSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

variable {R : Type u} [CommRing R] {p : ℕ}

private theorem localize_fraction (base : RingSplitting R p) (hp : 0 < p)
    (M : Submonoid R) (a : R) (s : M) :
    base.localize (S := Localization M) M hp (LocalizedModule.mk a s) =
      LocalizedModule.mk (base (a * (s : R) ^ (p - 1))) s := by
  change base.localize M hp (Localization.mk a s) = Localization.mk _ s
  rw [Localization.mk_eq_mk']
  have hrepr : IsLocalization.mk' (Localization M) (a * (s : R) ^ (p - 1)) (s ^ p) =
      IsLocalization.mk' (Localization M) a s := by
    rw [IsLocalization.mk'_eq_iff_eq']
    simp only [SubmonoidClass.coe_pow]
    congr 1
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
  rw [← hrepr, localize_mk']

private noncomputable def specSectionMap (base : RingSplitting R p) (hp : 0 < p)
    (U : (Spec (.of R)).Opens) (f : Γ(Spec (.of R), U)) : Γ(Spec (.of R), U) := by
  refine ⟨fun x ↦ base.localize (S := Localization x.1.asIdeal.primeCompl)
    x.1.asIdeal.primeCompl hp (f.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, a, s, hlocal⟩ := f.2 x
  refine ⟨V, hxV, i, base (a * s ^ (p - 1)), s, fun y ↦ ?_⟩
  obtain ⟨hs, hy⟩ := hlocal y
  refine ⟨hs, ?_⟩
  change base.localize (S := Localization y.1.asIdeal.primeCompl)
    y.1.asIdeal.primeCompl hp (f.1 (i y)) = _
  exact (congrArg (base.localize (S := Localization y.1.asIdeal.primeCompl)
    y.1.asIdeal.primeCompl hp) hy).trans
      (localize_fraction base hp y.1.asIdeal.primeCompl a ⟨s, hs⟩)

/-- A ring splitting defines a splitting on its affine spectrum. -/
noncomputable def toSpec (base : RingSplitting R p) (hp : 0 < p) :
    SchemeSplitting (Spec (.of R)) p where
  onOpen U :=
    { toAddMonoidHom :=
        { toFun := specSectionMap base hp U
          map_zero' := by
            apply Subtype.ext
            funext x
            exact (base.localize (S := Localization x.1.asIdeal.primeCompl)
              x.1.asIdeal.primeCompl hp).map_zero
          map_add' f g := by
            apply Subtype.ext
            funext x
            exact (base.localize (S := Localization x.1.asIdeal.primeCompl)
              x.1.asIdeal.primeCompl hp).map_add (f.1 x) (g.1 x) }
      map_pow_mul' f g := by
        apply Subtype.ext
        funext x
        exact (base.localize (S := Localization x.1.asIdeal.primeCompl)
          x.1.asIdeal.primeCompl hp).map_pow_mul (f.1 x) (g.1 x)
      map_one' := by
        apply Subtype.ext
        funext x
        exact (base.localize (S := Localization x.1.asIdeal.primeCompl)
          x.1.asIdeal.primeCompl hp).map_one }
  restrict_comm h f := by
    apply Subtype.ext
    funext x
    rfl

/-- The splitting on a spectrum acts by the localized splitting at each point. -/
theorem toSpec_apply (base : RingSplitting R p) (hp : 0 < p)
    (U : (Spec (.of R)).Opens) (f : Γ(Spec (.of R), U))
    (x : PrimeSpectrum R) (hx : x ∈ U) :
    (((base.toSpec hp).onOpen U f).1 ⟨x, hx⟩) =
      base.localize (S := Localization x.asIdeal.primeCompl)
        x.asIdeal.primeCompl hp (f.1 ⟨x, hx⟩) := rfl

/-- The splitting on a spectrum commutes with the map from its coordinate ring. -/
theorem toSpec_constant (base : RingSplitting R p) (hp : 0 < p)
    (U : (Spec (.of R)).Opens) (a : R) :
    (base.toSpec hp).onOpen U (StructureSheaf.toOpenₗ R R U a) =
      StructureSheaf.toOpenₗ R R U (base a) := by
  apply Subtype.ext
  funext x
  exact base.localize_algebraMap (x.1 : PrimeSpectrum R).asIdeal.primeCompl hp a

/-- A splitting of the global coordinate ring defines a splitting on an affine scheme. -/
noncomputable def toAffine {X : Scheme.{u}} [IsAffine X]
    (base : RingSplitting Γ(X, ⊤) p) (hp : 0 < p) : SchemeSplitting X p := by
  have := PresheafedSpace.c_isIso_of_iso X.isoSpec.inv.toPshHom
  exact (base.toSpec hp).pushforward X.isoSpec.inv

end FrobeniusSplitting.RingSplitting
