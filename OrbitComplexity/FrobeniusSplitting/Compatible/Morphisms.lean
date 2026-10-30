import OrbitComplexity.FrobeniusSplitting.Compatible.Schemes
import OrbitComplexity.FrobeniusSplitting.Splittings.Morphisms

/-!
# Compatible kernels of morphisms

A morphism commuting with two scheme splittings has a compatibly split
scheme-theoretic image. In particular, an ideal preserved by a ring splitting
defines a compatibly split closed image in its spectrum.

## Main results

* `FrobeniusSplitting.SchemeSplitting.isCompatible_ker`: compatible closed images.
* `FrobeniusSplitting.RingSplitting.toSpec_compatible_quotient`: compatible quotients.
-/

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme} {p : ℕ}

/-- A morphism commuting with splittings has a compatibly split scheme-theoretic image. -/
theorem isCompatible_ker (source : SchemeSplitting X p) (target : SchemeSplitting Y p)
    (f : X ⟶ Y) [QuasiCompact f]
    (hf : ∀ U s, source.onOpen (f ⁻¹ᵁ U) (f.app U s) = f.app U (target.onOpen U s)) :
    target.IsCompatible f.ker := by
  intro U a ha
  rw [Scheme.Hom.ker_apply] at ha ⊢
  change f.app U (target.onOpen U a) = 0
  rw [← hf]
  have ha : f.app U a = 0 := ha
  rw [ha, RingSplitting.map_zero]

end FrobeniusSplitting.SchemeSplitting

namespace FrobeniusSplitting.RingSplitting

open AlgebraicGeometry

universe u

/-- A compatible ideal defines a compatibly split closed image in the spectrum. -/
theorem toSpec_compatible_quotient {R : Type u} [CommRing R] {p : ℕ}
    (base : RingSplitting R p) (hp : 0 < p) (I : Ideal R) (hI : base.IsCompatible I) :
    (base.toSpec hp).IsCompatible
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker := by
  apply SchemeSplitting.isCompatible_ker ((base.quotient I hI).toSpec hp)
    (base.toSpec hp) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  intro U s
  exact base.toSpec_naturality (base.quotient I hI) hp (Ideal.Quotient.mk I)
    (base.quotient_mk I hI) U s

end FrobeniusSplitting.RingSplitting
