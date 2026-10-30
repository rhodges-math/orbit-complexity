import OrbitComplexity.FrobeniusSplitting.Normality.DenseOpen
import OrbitComplexity.FrobeniusSplitting.Normality.Sections
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Regular functions under proper birational morphisms

Regular functions on the source embed into the target function field through a
birational open subset. Properness makes them integral over affine target sections,
so normality of the target gives the structure-sheaf comparison.

## References

* Brion and Kumar, *Frobenius splitting methods in geometry and representation theory*,
  the structure-sheaf comparison used in the proof of Theorem 2.2.5.
-/

noncomputable section

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

private theorem integral_map_surjective {A B F : Type*} [CommRing A] [CommRing B]
    [CommRing F] [Algebra A F] [IsIntegrallyClosedIn A F]
    (φ : A →+* B) (j : B →+* F) (hj : Function.Injective j)
    (hcomp : j.comp φ = algebraMap A F) (hint : φ.IsIntegral) :
    Function.Surjective φ := by
  let : Algebra A B := φ.toAlgebra
  let k : B →ₐ[A] F := { j with commutes' := fun a ↦ RingHom.congr_fun hcomp a }
  intro b
  have hb0 : _root_.IsIntegral A b := hint b
  have hb : _root_.IsIntegral A (k b) := hb0.map k
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hb
  refine ⟨a, hj ?_⟩
  exact (RingHom.congr_fun hcomp a).trans ha

private theorem inclusion_field {Y : Scheme.{u}} [IsIntegral Y]
    (V : Y.Opens) [Nonempty V] :
    V.ι.appTop ≫ V.topIso.hom ≫ Y.germToFunctionField V =
      Y.germToFunctionField ⊤ := by
  have hres : V.ι.appTop ≫ V.topIso.hom =
      Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    exact (Y.presheaf.map_comp
      (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op
      (eqToHom V.ι_image_top.symm).op).symm
  rw [← Category.assoc, hres]
  ext s
  exact Y.presheaf.germ_res_apply (homOfLE le_top) _ _ s

private theorem affine_appTop_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsAffine Y] (f : X ⟶ Y) [UniversallyClosed f]
    (p : X.PartialIso Y)
    (hp : p.iso.hom ≫ p.target.ι = p.source.ι ≫ f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f.appTop := by
  let : Nonempty p.source := p.dense_source.nonempty.to_subtype
  let : Nonempty p.target := p.dense_target.nonempty.to_subtype
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let : Nonempty (p.source.ι ''ᵁ ⊤) := by
    simpa only [p.source.ι_image_top] using (inferInstance : Nonempty p.source)
  let j : Γ(X, ⊤) ⟶ Y.functionField :=
    p.source.ι.appTop ≫ p.iso.inv.appTop ≫ p.target.topIso.hom ≫
      Y.germToFunctionField p.target
  have hnat : f.appTop ≫ p.source.ι.appTop =
      p.target.ι.appTop ≫ p.iso.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hp]
  have hinv : p.iso.hom.appTop ≫ p.iso.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, p.iso.inv_hom_id, Scheme.Hom.id_appTop]
  have hfactor : f.appTop ≫ j = Y.germToFunctionField ⊤ := by
    calc
      f.appTop ≫ j =
          (f.appTop ≫ p.source.ι.appTop) ≫ p.iso.inv.appTop ≫
            p.target.topIso.hom ≫ Y.germToFunctionField p.target := by
              simp only [j, Category.assoc]
      _ = (p.target.ι.appTop ≫ p.iso.hom.appTop) ≫ p.iso.inv.appTop ≫
            p.target.topIso.hom ≫ Y.germToFunctionField p.target := by rw [hnat]
      _ = p.target.ι.appTop ≫ (p.iso.hom.appTop ≫ p.iso.inv.appTop) ≫
            p.target.topIso.hom ≫ Y.germToFunctionField p.target := by
              simp only [Category.assoc]
      _ = p.target.ι.appTop ≫ p.target.topIso.hom ≫
            Y.germToFunctionField p.target := by rw [hinv, Category.id_comp]
      _ = Y.germToFunctionField ⊤ := inclusion_field p.target
  have hj : Function.Injective j := by
    exact (Y.germToFunctionField_injective p.target).comp
      ((ConcreteCategory.bijective_of_isIso p.target.topIso.hom).1.comp
        ((ConcreteCategory.bijective_of_isIso (Scheme.Γ.mapIso p.iso.op).inv).1.comp
          (map_injective_of_isIntegral X (U := p.source.ι ''ᵁ ⊤) _)))
  have : IsIntegrallyClosedIn Γ(Y, ⊤) Y.functionField :=
    isIntegrallyClosedIn_functionField hn
  have hsurj : Function.Surjective f.appTop :=
    integral_map_surjective f.appTop.hom j.hom hj
      (congrArg CommRingCat.Hom.hom hfactor) (isIntegral_appTop_of_universallyClosed f)
  have hinj : Function.Injective f.appTop := by
    intro a b hab
    apply Y.germToFunctionField_injective ⊤
    exact (congrArg (fun φ : Γ(Y, ⊤) ⟶ Y.functionField ↦ φ a) hfactor).symm.trans
      ((congrArg j hab).trans
        (congrArg (fun φ : Γ(Y, ⊤) ⟶ Y.functionField ↦ φ b) hfactor))
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

private theorem birational_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Scheme.BirationalOver f (𝟙 Y)) (V : Y.Opens) :
    Scheme.BirationalOver (f ∣_ V) (𝟙 V.toScheme) := by
  obtain ⟨p, hp⟩ := h
  have hp' : p.iso.hom ≫ p.target.ι = p.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hp
  let g := p.source.ι ≫ f
  have : IsDominant p.source.ι := Opens.isDominant_ι p.dense_source
  have : IsDominant p.target.ι := Opens.isDominant_ι p.dense_target
  have : IsDominant g := by
    rw [show g = p.iso.hom ≫ p.target.ι from hp'.symm]
    infer_instance
  have : IsOpenImmersion g := by
    rw [show g = p.iso.hom ≫ p.target.ι from hp'.symm]
    infer_instance
  let a := p.source.ι ∣_ (f ⁻¹ᵁ V)
  let b := g ∣_ V
  have : IsDominant a := IsZariskiLocalAtTarget.restrict
    (P := @IsDominant) (show IsDominant p.source.ι from inferInstance) _
  have : IsDominant b := IsZariskiLocalAtTarget.restrict
    (P := @IsDominant) (show IsDominant g from inferInstance) _
  have hab : a ≫ f ∣_ V = b := (morphismRestrict_comp p.source.ι f V).symm
  exact (a.birationalOver (f ∣_ V) b hab).symm.trans
    (b.birationalOver (𝟙 V.toScheme) b (Category.comp_id _))

private theorem app_iso_of_restricted {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    [h : IsIso (f ∣_ V).appTop] : IsIso (f.app V) := by
  rw [morphismRestrict_appTop] at h
  let e := X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V ⊤)).op
  have h' : IsIso (f.app (V.ι ''ᵁ ⊤)) :=
    (isIso_comp_right_iff (f.app (V.ι ''ᵁ ⊤)) e.hom).mp h
  rwa [Scheme.Opens.ι_image_top] at h'

private theorem affine_app_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] (h : Scheme.BirationalOver f (𝟙 Y))
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : Y.Opens) (hV : IsAffineOpen V) : IsIso (f.app V) := by
  rcases isEmpty_or_nonempty V with hempty | hnonempty
  · have : IsEmpty V.toScheme := hempty
    have : IsIso (f ∣_ V) := inferInstance
    exact app_isIso_of_restrict f V
  · obtain ⟨p, hp⟩ := birational_restrict f h V
    have : Nonempty p.target := p.dense_target.nonempty.to_subtype
    have : Nonempty p.source := Nonempty.map p.iso.inv inferInstance
    have : Nonempty (f ⁻¹ᵁ V).toScheme := Nonempty.map p.source.ι inferInstance
    have : IsIntegral (f ⁻¹ᵁ V).toScheme := inferInstance
    have : IsAffine V.toScheme := hV
    have hnV (y : V.toScheme) : IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := by
      have := hn (V.ι y)
      exact IsIntegrallyClosed.of_equiv
        (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
    have hp' : p.iso.hom ≫ p.target.ι = p.source.ι ≫ f ∣_ V := by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hp
    have : IsIso (f ∣_ V).appTop := affine_appTop_iso (f ∣_ V) p hp' hnV
    exact app_iso_of_restricted f V

/-- A proper birational morphism to a normal integral scheme preserves regular functions. -/
theorem proper_birational_sheaf {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] (h : Scheme.BirationalOver f (𝟙 Y))
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f.c := by
  let φ : Y.𝒪 ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.𝒪 :=
    ⟨f.c⟩
  have : IsIso φ := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun V : Y.affineOpens ↦ V.1)
    · simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using Y.isBasis_affineOpens
    · intro V
      exact affine_app_iso f h hn V.1 V.2
  exact (TopCat.Sheaf.forget CommRingCat (Y : TopCat)).map_isIso φ

end FrobeniusSplitting
