import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorCoordinateEvaluation
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateCocone
import Batteries.Tactic.Lint

/-!
# Scalar maps in affine coordinate presentations

A morphism between two scalar extensions restricts to the same original affine
open on each side. Its regular-function map is the tensor-evaluation comparison,
which gives the corresponding square between affine coordinate spectra.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace FrobeniusSplitting

private theorem iso_square_cancel {C : Type*} [Category C]
    {A B X Y : C} (a : A ≅ X) (b : B ≅ Y)
    (v : A ⟶ B) (m : X ⟶ Y) (h : a.hom ≫ m = v ≫ b.hom) :
    a.inv ≫ v = m ≫ b.inv := by
  apply (cancel_mono b.hom).mp
  have H := congrArg (fun f : A ⟶ Y => a.inv ≫ f) h.symm
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using H

/-- A commutative ring-coordinate comparison gives the square of its affine
scheme presentations. The coordinate isomorphisms are compared before inversion. -/
theorem affineCoordinateSquare {A B : CommRingCat.{u}}
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (a : A ≅ Γ(X, ⊤)) (b : B ≅ Γ(Y, ⊤)) (v : A ⟶ B) (m : Y ⟶ X)
    (h : a.hom ≫ m.appTop = v ≫ b.hom) :
    Spec.map v ≫ Spec.map a.inv ≫ X.isoSpec.inv =
      Spec.map b.inv ≫ Y.isoSpec.inv ≫ m := by
  have hring : a.inv ≫ v = m.appTop ≫ b.inv :=
    iso_square_cancel a b v m.appTop h
  calc
    Spec.map v ≫ Spec.map a.inv ≫ X.isoSpec.inv =
        Spec.map (a.inv ≫ v) ≫ X.isoSpec.inv := by
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (m.appTop ≫ b.inv) ≫ X.isoSpec.inv :=
      congrArg (fun f : Γ(X, ⊤) ⟶ B => Spec.map f ≫ X.isoSpec.inv) hring
    _ = Spec.map b.inv ≫ Y.isoSpec.inv ≫ m := by
      rw [Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality]

private theorem restriction_comparison {Y YR YK : Scheme.{u}}
    (qR : YR ⟶ Y) (qK : YK ⟶ Y) (m : YK ⟶ YR)
    (hm : m ≫ qR = qK) (U : Y.Opens) :
    ∃ d : (qK ⁻¹ᵁ U).toScheme ⟶ (qR ⁻¹ᵁ U).toScheme,
      d ≫ (qR ∣_ U) = qK ∣_ U ∧
      d ≫ (qR ⁻¹ᵁ U).ι = (qK ⁻¹ᵁ U).ι ≫ m ∧
      IsPullback d (qK ⁻¹ᵁ U).ι (qR ⁻¹ᵁ U).ι m := by
  let T := isPullback_morphismRestrict qR U
  have hw : (qK ∣_ U) ≫ U.ι = ((qK ⁻¹ᵁ U).ι ≫ m) ≫ qR := by
    rw [morphismRestrict_ι, Category.assoc, hm]
  let d : (qK ⁻¹ᵁ U).toScheme ⟶ (qR ⁻¹ᵁ U).toScheme :=
    T.lift (qK ∣_ U) ((qK ⁻¹ᵁ U).ι ≫ m) hw
  have hf : d ≫ (qR ∣_ U) = qK ∣_ U := T.lift_fst _ _ _
  have hs : d ≫ (qR ⁻¹ᵁ U).ι = (qK ⁻¹ᵁ U).ι ≫ m := T.lift_snd _ _ _
  have H : IsPullback (d ≫ (qR ∣_ U)) (qK ⁻¹ᵁ U).ι U.ι (m ≫ qR) := by
    rw [hf, hm]
    exact isPullback_morphismRestrict qK U
  exact ⟨d, hf, hs, H.of_right hs T⟩

private theorem extend_chart_data {D : Sort*} {A B C Q : D → Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d)
    (next : ∀ d, A d → B d → C d → Q d) :
    ∃ d : D, A d ∧ B d ∧ C d ∧ Q d := by
  obtain ⟨d, ha, hb, hc⟩ := h
  exact ⟨d, ha, hb, hc, next d ha hb hc⟩

end FrobeniusSplitting
