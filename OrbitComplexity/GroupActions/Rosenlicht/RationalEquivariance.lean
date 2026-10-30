import OrbitComplexity.GroupActions.Rosenlicht.FieldActions
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Equivariance of rational maps

Precomposition with an automorphism translates the domain of a partial map.
Equivariance means equality of the resulting rational maps, and hence does not
require any chosen domain to be stable under the action.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u v

variable {X Y : Scheme.{u}} {M : Type v} [Monoid M]

/-- Precomposition of a partial map with an automorphism, on the inverse image
of its domain. -/
def partialMapPrecompose (p : X.PartialMap Y) (e : X ≅ X) : X.PartialMap Y where
  domain := e.hom ⁻¹ᵁ p.domain
  dense_domain := p.dense_domain.preimage e.hom.homeomorph.isOpenMap
  hom := (e.hom ∣_ p.domain) ≫ p.hom

/-- A partial map is equivariant when inverse translations commute with its
rational map. The equality allows the translated domains to differ. -/
def RationalEquivariant (ρ : M →* Aut X) (σ : M →* Aut Y)
    (p : X.PartialMap Y) : Prop :=
  ∀ m, (partialMapPrecompose p (ρ m).symm).toRationalMap =
    (p.compHom (σ m).inv).toRationalMap

private lemma spec_stalkCongr (x y : Y) (h : x = y) :
    Spec.map (Y.presheaf.stalkCongr (.of_eq h)).hom ≫ Y.fromSpecStalk x =
      Y.fromSpecStalk y := by
  subst y
  change Spec.map (Y.presheaf.stalkSpecializes (specializes_refl x)) ≫
    Y.fromSpecStalk x = Y.fromSpecStalk x
  rw [TopCat.Presheaf.stalkSpecializes_refl, Spec.map_id, Category.id_comp]

/-- The map on spectra induced by function-field pullback commutes with the
canonical morphisms from the generic stalks. -/
theorem functionFieldMap_genericPoint [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] :
    Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫
        Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ f := by
  change Spec.map ((Y.presheaf.stalkCongr (.of_eq (map_genericPoint f).symm)).hom ≫
    f.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) = _
  rw [Spec.map_comp, Category.assoc, spec_stalkCongr _ _ (map_genericPoint f).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

/-- Translating a partial map pulls its generic restriction back along the same
scheme automorphism. -/
theorem partialMapPrecompose_generic [IrreducibleSpace X]
    (p : X.PartialMap Y) (e : X ≅ X) :
    (partialMapPrecompose p e).fromFunctionField =
      Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫ p.fromFunctionField := by
  change (e.hom ⁻¹ᵁ p.domain).fromSpecStalkOfMem (genericPoint X) _ ≫
      (e.hom ∣_ p.domain) ≫ p.hom =
    Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫
      p.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ p.hom
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun g ↦ g ≫ p.hom)
  apply (cancel_mono p.domain.ι).mp
  simp only [Category.assoc, morphismRestrict_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]
  erw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
  exact (functionFieldMap_genericPoint e.hom).symm

/-- Equivariance of rational maps implies the commutative translation diagram
on their generic restrictions. -/
theorem rationalEquivariant_generic [IrreducibleSpace X]
    (ρ : M →* Aut X) (σ : M →* Aut Y) (p : X.PartialMap Y)
    (hp : RationalEquivariant ρ σ p) (m : M) :
    Spec.map (CommRingCat.ofHom (functionFieldMap (ρ m).inv)) ≫ p.fromFunctionField =
      p.fromFunctionField ≫ (σ m).inv := by
  have he := congrArg Scheme.RationalMap.fromFunctionField (hp m)
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMapPrecompose_generic] at he
  exact he

end

end GroupActions
