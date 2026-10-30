import OrbitComplexity.FrobeniusSplitting.Normality.FlatDescent
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Normal local rings in fibres of pointed smooth products

A smooth pointed factor makes the product projection flat and surjective.
Smoothness of the total product then gives normal domain stalks on every field
fibre of the other factor by faithfully flat descent.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory
noncomputable section
namespace FrobeniusSplitting
universe u

private theorem sectioned_flat_fibre_stalks {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (base : Y ⟶ S) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    [Flat f] [Smooth (f ≫ base)]
    (L : Type u) [Field L] (t : Spec (.of L) ⟶ S) :
    ∀ z : (pullback base t : Scheme.{u}),
      IsDomain ((pullback base t : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback base t : Scheme.{u}).presheaf.stalk z) := by
  let P : Scheme.{u} := pullback base t
  let q : pullback f (pullback.fst base t) ⟶ P :=
    pullback.snd f (pullback.fst base t)
  let sigma : P ⟶ pullback f (pullback.fst base t) :=
    pullback.lift (pullback.fst base t ≫ s) (𝟙 P) (by
      simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have hsec : sigma ≫ q = 𝟙 P := pullback.lift_snd _ _ _
  have : Surjective q := ⟨by
    intro z
    exact ⟨sigma z, congrArg (fun k : P ⟶ P => k z) hsec⟩⟩
  have : Smooth (q ≫ pullback.snd base t) := by
    rw [← pullbackRightPullbackFstIso_hom_snd base t f]
    infer_instance
  exact stalks_of_flat_surjective q
    (stalks_of_smooth (q ≫ pullback.snd base t))

/-- A smooth product with a smooth pointed factor gives normal domain local rings
on every field fibre of the other factor, over an arbitrary base scheme. -/
theorem stalks_fibres_of_smooth_product {S : Scheme.{u}} (H Z : Over S)
    (e : S ⟶ H.left) (he : e ≫ H.hom = 𝟙 S)
    [Smooth H.hom] [Smooth (H ⊗ Z).hom]
    (L : Type u) [Field L] (t : Spec (CommRingCat.of L) ⟶ S) :
    ∀ z : (pullback Z.hom t : Scheme.{u}),
      IsDomain ((pullback Z.hom t : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback Z.hom t : Scheme.{u}).presheaf.stalk z) := by
  let p : (H ⊗ Z).left ⟶ Z.left := pullback.snd H.hom Z.hom
  let s : Z.left ⟶ (H ⊗ Z).left :=
    pullback.lift (Z.hom ≫ e) (𝟙 Z.left) (by
      simp only [Category.assoc, he, Category.comp_id, Category.id_comp])
  have hs : s ≫ p = 𝟙 Z.left := pullback.lift_snd _ _ _
  have : Smooth (p ≫ Z.hom) := by
    change Smooth (pullback.snd H.hom Z.hom ≫ Z.hom)
    rw [← pullback.condition]
    exact inferInstanceAs (Smooth (H ⊗ Z).hom)
  exact sectioned_flat_fibre_stalks p Z.hom s hs L t

end FrobeniusSplitting
end
