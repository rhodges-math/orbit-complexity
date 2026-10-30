import OrbitComplexity.GroupActions.Varieties.Differentials
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Differential maps on cotangent fibers

The universal property of differentials identifies scalar-valued derivations with dual
cotangent fibers. Precomposition of derivations agrees with the dual differential map.

## Main definitions

* `GroupActions.cotangentDualDerivation`: the dual-fiber interpretation of derivations.
* `GroupActions.cotangentFiberMap`: the differential map at a coefficient algebra.

## Main results

* `GroupActions.cotangentDualDerivation_comp`: naturality under algebra morphisms.
* `GroupActions.smooth_of_surjective_derivations`: surjective derivation maps detect smoothness.
* `GroupActions.etale_of_bijective_derivations`: bijective derivation maps detect étaleness.
* `GroupActions.openImmersion_of_etale`: an étale universally injective map is an open immersion.
-/

open KaehlerDifferential
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w

variable (R : Type u) (S : Type v) (L : Type w)
  [CommRing R] [CommRing S] [CommRing L]
  [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

/-- The dual of a cotangent fiber is the module of derivations into its coefficient algebra. -/
def cotangentDualDerivation :
    Module.Dual L (L ⊗[S] Ω[S⁄R]) ≃ₗ[L] Derivation R S L where
  toEquiv := (LinearMap.liftBaseChangeEquiv L).symm.toEquiv.trans
    (KaehlerDifferential.linearMapEquivDerivation R S).toEquiv
  map_add' f g := by
    apply Derivation.ext
    intro s
    change (f + g) (1 ⊗ₜ[S] D R S s) = f (1 ⊗ₜ[S] D R S s) + g (1 ⊗ₜ[S] D R S s)
    rfl
  map_smul' l f := by
    apply Derivation.ext
    intro s
    change (l • f) (1 ⊗ₜ[S] D R S s) = l • f (1 ⊗ₜ[S] D R S s)
    rfl

/-- The derivation associated to a cotangent functional evaluates it on universal differentials. -/
@[simp]
theorem cotangentDualDerivation_apply (f : Module.Dual L (L ⊗[S] Ω[S⁄R])) (s : S) :
    cotangentDualDerivation R S L f s = f (1 ⊗ₜ[S] D R S s) := rfl

end

noncomputable section

universe z

variable (R : Type u) (S : Type v) (T : Type w) (L : Type z)
  [CommRing R] [CommRing S] [CommRing T] [CommRing L]
  [Algebra R S] [Algebra R T] [Algebra R L] [Algebra S T] [Algebra S L] [Algebra T L]
  [IsScalarTower R S T] [IsScalarTower R S L] [IsScalarTower R T L] [IsScalarTower S T L]

/-- The map on cotangent fibers induced by a morphism of algebras. -/
def cotangentFiberMap : L ⊗[S] Ω[S⁄R] →ₗ[L] L ⊗[T] Ω[T⁄R] :=
  (((TensorProduct.mk T L Ω[T⁄R] 1).restrictScalars S) ∘ₗ
    KaehlerDifferential.map R R S T).liftBaseChange L

omit [Algebra R L] [IsScalarTower R S L] [IsScalarTower R T L] in
/-- On pure tensors, the fiber map is the scalar extension of the differential map. -/
@[simp]
theorem cotangentFiberMap_tmul (l : L) (ω : Ω[S⁄R]) :
    cotangentFiberMap R S T L (l ⊗ₜ[S] ω) =
      l • (1 ⊗ₜ[T] KaehlerDifferential.map R R S T ω) := rfl

omit [Algebra R L] [IsScalarTower R S L] [IsScalarTower R T L] in
/-- The fiber map agrees with base change followed by tensor cancellation. -/
theorem cotangentFiberMap_baseChange :
    cotangentFiberMap R S T L =
      (KaehlerDifferential.mapBaseChange R S T).baseChange L ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange S T L L Ω[S⁄R]).symm.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro l ω
  simp only [cotangentFiberMap_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Precomposing a derivation corresponds to the dual map on cotangent fibers. -/
theorem cotangentDualDerivation_comp
    (f : Module.Dual L (L ⊗[T] Ω[T⁄R])) :
    cotangentDualDerivation R S L ((cotangentFiberMap R S T L).dualMap f) =
      (cotangentDualDerivation R T L f).compAlgebraMap S := by
  apply Derivation.ext
  intro s
  simp only [cotangentDualDerivation_apply, LinearMap.dualMap_apply, cotangentFiberMap_tmul,
    KaehlerDifferential.map_D, one_smul, Derivation.compAlgebraMap_apply]

end


/-- An étale universally injective morphism is an open immersion. -/
theorem openImmersion_of_etale {X Y : Scheme} (f : X ⟶ Y) [Etale f]
    [UniversallyInjective f] : IsOpenImmersion f := by
  have : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  have : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f


noncomputable section

universe u v w z

variable (R : Type u) (S : Type v) (T : Type w) (L : Type z)
  [CommRing R] [CommRing S] [CommRing T] [CommRing L]
  [Algebra R S] [Algebra R T] [Algebra R L] [Algebra S T] [Algebra S L] [Algebra T L]
  [IsScalarTower R S T] [IsScalarTower R S L] [IsScalarTower R T L] [IsScalarTower S T L]

/-- Precomposition is surjective on derivations exactly when the dual fiber map is surjective. -/
theorem surjective_compAlgebraMap_iff :
    Function.Surjective (fun d : Derivation R T L => d.compAlgebraMap S) ↔
      Function.Surjective (cotangentFiberMap R S T L).dualMap := by
  constructor
  · intro h f
    obtain ⟨d, hd⟩ := h (cotangentDualDerivation R S L f)
    refine ⟨(cotangentDualDerivation R T L).symm d, ?_⟩
    apply (cotangentDualDerivation R S L).injective
    rw [cotangentDualDerivation_comp, LinearEquiv.apply_symm_apply]
    exact hd
  · intro h d
    obtain ⟨f, hf⟩ := h ((cotangentDualDerivation R S L).symm d)
    refine ⟨cotangentDualDerivation R T L f, ?_⟩
    change (cotangentDualDerivation R T L f).compAlgebraMap S = d
    rw [← cotangentDualDerivation_comp, hf, LinearEquiv.apply_symm_apply]

/-- Precomposition is bijective on derivations exactly when the dual fiber map is bijective. -/
theorem bijective_compAlgebraMap_iff :
    Function.Bijective (fun d : Derivation R T L => d.compAlgebraMap S) ↔
      Function.Bijective (cotangentFiberMap R S T L).dualMap := by
  constructor
  · intro h
    refine ⟨?_, (surjective_compAlgebraMap_iff R S T L).mp h.surjective⟩
    intro f g hfg
    apply (cotangentDualDerivation R T L).injective
    apply h.injective
    change (cotangentDualDerivation R T L f).compAlgebraMap S =
      (cotangentDualDerivation R T L g).compAlgebraMap S
    rw [← cotangentDualDerivation_comp, ← cotangentDualDerivation_comp, hfg]
  · intro h
    refine ⟨?_, (surjective_compAlgebraMap_iff R S T L).mpr h.surjective⟩
    intro d e hde
    apply (cotangentDualDerivation R T L).symm.injective
    apply h.injective
    apply (cotangentDualDerivation R S L).injective
    simpa only [cotangentDualDerivation_comp, LinearEquiv.apply_symm_apply] using hde

end

section Algebras

variable (R : Type u) (S : Type v) (T : Type w)
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Surjective precomposition on all residue-field-valued derivations detects smoothness. -/
theorem smooth_of_surjective_derivations [Algebra.Smooth R S] [Algebra.Smooth R T]
    [Algebra.FinitePresentation S T]
    (hmap : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Surjective
      (fun d : Derivation R T (IsLocalRing.ResidueField (Localization.AtPrime ideal)) =>
        d.compAlgebraMap S)) : Algebra.Smooth S T := by
  apply smooth_of_surjective_dual_map R S T
  intro ideal hmaximal
  have h := (surjective_compAlgebraMap_iff R S T
    (IsLocalRing.ResidueField (Localization.AtPrime ideal))).mp (hmap ideal)
  rw [cotangentFiberMap_baseChange, ← LinearMap.dualMap_comp_dualMap] at h
  change Function.Surjective
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S T
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))
        (IsLocalRing.ResidueField (Localization.AtPrime ideal)) Ω[S⁄R]).symm.dualMap ∘
      ((KaehlerDifferential.mapBaseChange R S T).baseChange
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))).dualMap) at h
  simpa only [EquivLike.comp_surjective] using h

/-- Bijective precomposition on all residue-field-valued derivations detects étaleness. -/
theorem etale_of_bijective_derivations [Algebra.Smooth R S] [Algebra.Smooth R T]
    [Algebra.FinitePresentation S T]
    (hmap : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Bijective
      (fun d : Derivation R T (IsLocalRing.ResidueField (Localization.AtPrime ideal)) =>
        d.compAlgebraMap S)) : Algebra.Etale S T := by
  apply etale_of_bijective_dual_map R S T
  intro ideal hmaximal
  have h := (bijective_compAlgebraMap_iff R S T
    (IsLocalRing.ResidueField (Localization.AtPrime ideal))).mp (hmap ideal)
  rw [cotangentFiberMap_baseChange, ← LinearMap.dualMap_comp_dualMap] at h
  change Function.Bijective
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S T
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))
        (IsLocalRing.ResidueField (Localization.AtPrime ideal)) Ω[S⁄R]).symm.dualMap ∘
      ((KaehlerDifferential.mapBaseChange R S T).baseChange
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))).dualMap) at h
  simpa only [EquivLike.comp_bijective] using h

end Algebras

end GroupActions
