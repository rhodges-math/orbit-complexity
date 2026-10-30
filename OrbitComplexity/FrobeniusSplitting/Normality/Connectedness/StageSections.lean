import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent

/-!
# Canonical scalar-stage sections of an original section

-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

/-- The spectrum of an algebra augmentation is a section of its structure map. -/
def algebraOriginSection {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) : Spec (.of R) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom ε.toRingHom)

/-- The augmentation section has its exact original scalar triangle. -/
theorem algebraOriginSection_base {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) :
    algebraOriginSection ε ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      𝟙 (Spec (.of R)) := by
  have h : ε.toRingHom.comp (algebraMap R A) = RingHom.id R := by
    apply RingHom.ext
    intro r
    exact ε.commutes r
  rw [algebraOriginSection, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h,
    CommRingCat.ofHom_id, Spec.map_id]

/-- Pull back the specified section along the specified base morphism. -/
def pullbackSection {B X T : Scheme.{u}}
    (κ : B ⟶ T) (a : X ⟶ T) (s : T ⟶ X) (hs : s ≫ a = 𝟙 T) :
    B ⟶ pullback κ a :=
  pullback.lift (𝟙 B) (κ ≫ s) (by
    simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- The pulled-back section remains a section of the base projection. -/
theorem pullbackSection_base {B X T : Scheme.{u}}
    (κ : B ⟶ T) (a : X ⟶ T) (s : T ⟶ X) (hs : s ≫ a = 𝟙 T) :
    pullbackSection κ a s hs ≫ pullback.fst κ a = 𝟙 B :=
  pullback.lift_fst _ _ _

/-- The pulled-back section retains its specified original image. -/
theorem pullbackSection_original {B X T : Scheme.{u}}
    (κ : B ⟶ T) (a : X ⟶ T) (s : T ⟶ X) (hs : s ≫ a = 𝟙 T) :
    pullbackSection κ a s hs ≫ pullback.snd κ a = κ ≫ s :=
  pullback.lift_snd _ _ _

private theorem pullbackSection_natural
    {B C X T : Scheme.{u}} (κ : B ⟶ T) (κ' : C ⟶ T) (ρ : C ⟶ B)
    (hρ : ρ ≫ κ = κ') (a : X ⟶ T) (s : T ⟶ X) (hs : s ≫ a = 𝟙 T)
    (t : pullback κ' a ⟶ pullback κ a)
    (ht₀ : t ≫ pullback.fst κ a = pullback.fst κ' a ≫ ρ)
    (ht₁ : t ≫ pullback.snd κ a = pullback.snd κ' a) :
    ρ ≫ pullbackSection κ a s hs = pullbackSection κ' a s hs ≫ t := by
  apply pullback.hom_ext
  · calc
      (ρ ≫ pullbackSection κ a s hs) ≫ pullback.fst κ a = ρ := by
        rw [Category.assoc, pullbackSection_base, Category.comp_id]
      _ = (pullbackSection κ' a s hs ≫ pullback.fst κ' a) ≫ ρ := by
        rw [pullbackSection_base, Category.id_comp]
      _ = pullbackSection κ' a s hs ≫ (pullback.fst κ' a ≫ ρ) := Category.assoc _ _ _
      _ = pullbackSection κ' a s hs ≫ (t ≫ pullback.fst κ a) :=
        congrArg (fun q => pullbackSection κ' a s hs ≫ q) ht₀.symm
      _ = (pullbackSection κ' a s hs ≫ t) ≫ pullback.fst κ a :=
        (Category.assoc _ _ _).symm
  · calc
      (ρ ≫ pullbackSection κ a s hs) ≫ pullback.snd κ a =
          ρ ≫ (κ ≫ s) := by rw [Category.assoc, pullbackSection_original]
      _ = κ' ≫ s := by rw [← Category.assoc, hρ]
      _ = (pullbackSection κ' a s hs ≫ t) ≫ pullback.snd κ a := by
        rw [Category.assoc, ht₁, pullbackSection_original]

variable {K : Type u} [CommRing K] (S : Subalgebra ℤ K)

/-- The canonical section on the original generic scalar pullback. -/
def genericOriginSection {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _) :
    Spec (.of K) ⟶ (genericScalarModel S a).left :=
  pullbackSection (Spec.map (CommRingCat.ofHom (algebraMap S K))) a s hs

/-- The canonical section on a specified finite scalar stage. -/
def stageOriginSection {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _) (i : CoefficientStage S) :
    Spec (.of i.val) ⟶ (stageScalarModel S a i).left :=
  pullbackSection
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) a s hs

/-- Each specified finite-stage origin is a section of the original stage structure. -/
theorem stageOriginSection_base {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _) (i : CoefficientStage S) :
    stageOriginSection S a s hs i ≫ (stageScalarModel S a i).hom = 𝟙 _ :=
  pullbackSection_base _ _ _ _

/-- The finite-stage section and the original generic section agree after
the specified generic scalar-cone projection. -/
theorem stageOriginSection_comparison {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _) (i : CoefficientStage S) :
    Spec.map (CommRingCat.ofHom (algebraMap i.val K)) ≫ stageOriginSection S a s hs i =
      genericOriginSection S a s hs ≫ (modelScalarCone S a).π.app (op i) := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κK := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap i.val K))
  have hρ : ρ ≫ κi = κK := by
    rw [← Spec.map_comp]
    rfl
  have hfst : (modelScalarCone S a).π.app (op i) ≫ (stageScalarModel S a i).hom =
      (genericScalarModel S a).hom ≫ ρ := by
    change pullback.lift _ _ _ ≫ pullback.fst _ a = _
    exact pullback.lift_fst _ _ _
  have hsnd : (modelScalarCone S a).π.app (op i) ≫ pullback.snd κi a =
      pullback.snd κK a := by
    change pullback.lift _ _ _ ≫ pullback.snd _ a = _
    exact pullback.lift_snd _ _ _
  exact pullbackSection_natural κi κK ρ hρ a s hs
    ((modelScalarCone S a).π.app (op i)) hfst hsnd

end FrobeniusSplitting
