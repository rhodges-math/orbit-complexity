import OrbitComplexity.GroupActions.Rosenlicht.InvariantMaps

/-!
# Coordinates of partial maps

The generic restriction of a partial map determines the rational germs of its affine
coordinate functions.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

/-- A coordinate of a partial map to an affine spectrum has the prescribed
generic value whenever the partial map extends that generic morphism. -/
theorem partialMap_coordinate_germ (X : Scheme.{u}) [IrreducibleSpace X]
    (A : CommRingCat.{u}) (r : X.PartialMap (Spec A))
    (φ : A →+* X.functionField)
    (hf : r.fromFunctionField = Spec.map (CommRingCat.ofHom φ)) (a : A) :
    letI : Nonempty r.domain := Set.nonempty_coe_sort.mpr r.dense_domain.nonempty
    X.germToFunctionField r.domain
      (r.domain.topIso.hom (r.hom.appTop ((Scheme.ΓSpecIso A).inv a))) = φ a := by
  have : Nonempty r.domain := Set.nonempty_coe_sort.mpr r.dense_domain.nonempty
  let ψ : A ⟶ Γ(X, r.domain) :=
    (Scheme.ΓSpecIso A).inv ≫ r.hom.appTop ≫ r.domain.topIso.hom
  have hψ : r.domain.toSpecΓ ≫ Spec.map ψ = r.hom := by
    calc
      _ = r.domain.toScheme.toSpecΓ ≫
          Spec.map ((Scheme.ΓSpecIso A).inv ≫ r.hom.appTop) := by
        dsimp only [Scheme.Opens.toSpecΓ, ψ]
        simp only [Spec.map_comp, Category.assoc]
        rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
      _ = r.hom := by
        rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
          Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hspec : Spec.map (ψ ≫ X.germToFunctionField r.domain) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [Spec.map_comp, ← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
      Category.assoc, hψ]
    exact hf
  have he := Spec.map_injective hspec
  exact congrArg (fun f : A ⟶ X.functionField ↦ f a) he

end

end GroupActions
