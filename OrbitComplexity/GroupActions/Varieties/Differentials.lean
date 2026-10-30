import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Projective

/-! # Differentials and étale morphisms

The Jacobi–Zariski exact sequence detects formal étaleness from the base-change map
on Kähler differentials. This criterion applies to morphisms between smooth affine charts.

## Main results

* `GroupActions.formallyEtale_of_bijective_map`: a bijective differential map and vanishing
  first cotangent homology imply formal étaleness.
* `GroupActions.linearMap_bijective_of_fibers`: bijectivity of a map between finite flat
  modules can be checked at maximal residue fields.
* `GroupActions.etale_of_bijective_dual_map`: bijective dual differential maps imply étaleness
  for a finitely presented morphism between smooth algebras.
* `GroupActions.smooth_of_surjective_dual_map`: surjective dual differential maps imply
  smoothness for a finitely presented morphism between smooth algebras.

## References

* The Stacks Project, Tags 00S2 and 00UQ.
-/

namespace GroupActions

open KaehlerDifferential
open scoped TensorProduct

universe u v w

variable (R : Type u) (S : Type v) (T : Type w)
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- A bijective base-change map on differentials gives formal étaleness when the first
cotangent homology over the base ring vanishes. -/
theorem formallyEtale_of_bijective_map
    [Subsingleton (Algebra.H1Cotangent R T)]
    (hmap : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hkaehler (x : Ω[T⁄S]) : x = 0 := by
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    obtain ⟨z, hz⟩ := hmap.surjective y
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T y).mpr ⟨z, hz⟩
  have hdelta (x : Algebra.H1Cotangent S T) : Algebra.H1Cotangent.δ R S T x = 0 := by
    apply hmap.injective
    rw [map_zero]
    exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
  have hcotangent (x : Algebra.H1Cotangent S T) : x = 0 := by
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hdelta x)
    calc
      x = Algebra.H1Cotangent.map R S T T y := hy.symm
      _ = Algebra.H1Cotangent.map R S T T 0 :=
        congrArg _ (Subsingleton.elim y 0)
      _ = 0 := map_zero _
  exact ⟨⟨fun x y => (hkaehler x).trans (hkaehler y).symm⟩,
    ⟨fun x y => (hcotangent x).trans (hcotangent y).symm⟩⟩

section LocalModules

variable {A M N : Type*} [CommRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [Module.Finite A M] [Module.Finite A N] [Module.Flat A M] [Module.Flat A N]

/-- A map between finite flat modules over a local ring is bijective when its reduction
modulo the maximal ideal is bijective. -/
theorem linearMap_bijective_of_residue (f : M →ₗ[A] N)
    (hmap : Function.Bijective (f.lTensor (IsLocalRing.ResidueField A))) :
    Function.Bijective f := by
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  have : Module.Free A N := Module.free_of_flat_of_isLocalRing
  obtain ⟨g, hgf⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hmap.injective
  have htensor : g.lTensor (IsLocalRing.ResidueField A) ∘ₗ
      f.lTensor (IsLocalRing.ResidueField A) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hgf, LinearMap.lTensor_id]
  have hright : Function.RightInverse (g.lTensor (IsLocalRing.ResidueField A))
      (f.lTensor (IsLocalRing.ResidueField A)) := by
    intro y
    obtain ⟨x, rfl⟩ := hmap.surjective y
    exact congrArg (f.lTensor (IsLocalRing.ResidueField A)) (LinearMap.congr_fun htensor x)
  obtain ⟨h, hhg⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective g).mpr hright.injective
  have hleft : Function.LeftInverse g f := fun x => LinearMap.congr_fun hgf x
  have hg : Function.Injective g :=
    (show Function.LeftInverse h g from fun x => LinearMap.congr_fun hhg x).injective
  exact ⟨hleft.injective, fun y => ⟨g y, hg (hleft (g y))⟩⟩

end LocalModules

section ModuleFibers

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [Module.Finite A M] [Module.Finite A N] [Module.Flat A M] [Module.Flat A N]

/-- A map between finite flat modules is bijective if its maps on all maximal residue
fields are bijective. -/
theorem linearMap_bijective_of_fibers (f : M →ₗ[A] N)
    (hmap : ∀ (ideal : Ideal A) [ideal.IsMaximal], Function.Bijective
      (f.baseChange (IsLocalRing.ResidueField (Localization.AtPrime ideal)))) :
    Function.Bijective f := by
  apply bijective_of_isLocalized_maximal
    (fun ideal _ => Localization.AtPrime ideal ⊗[A] M)
    (fun ideal _ => TensorProduct.mk A (Localization.AtPrime ideal) M 1)
    (fun ideal _ => Localization.AtPrime ideal ⊗[A] N)
    (fun ideal _ => TensorProduct.mk A (Localization.AtPrime ideal) N 1) f
  intro ideal hmaximal
  have heq : IsLocalizedModule.map ideal.primeCompl
      (TensorProduct.mk A (Localization.AtPrime ideal) M 1)
      (TensorProduct.mk A (Localization.AtPrime ideal) N 1) f =
      (f.baseChange (Localization.AtPrime ideal)).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext ideal.primeCompl
      (TensorProduct.mk A (Localization.AtPrime ideal) M 1)
      (TensorProduct.mk A (Localization.AtPrime ideal) N 1)
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [IsLocalizedModule.map_apply]
    change (1 : Localization.AtPrime ideal) ⊗ₜ[A] f x =
      (f.baseChange (Localization.AtPrime ideal)) (1 ⊗ₜ[A] x)
    rw [LinearMap.baseChange_tmul]
  rw [heq]
  change Function.Bijective (f.baseChange (Localization.AtPrime ideal))
  apply linearMap_bijective_of_residue
  change Function.Bijective ((f.baseChange (Localization.AtPrime ideal)).baseChange
    (IsLocalRing.ResidueField (Localization.AtPrime ideal)))
  rw [LinearMap.baseChange_baseChange]
  simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.bijective_comp] using hmap ideal

end ModuleFibers

/-- A morphism between smooth algebras is étale if it is of finite presentation and the
maps dual to its differential maps at all maximal residue fields are bijective. -/
theorem etale_of_bijective_dual_map [Algebra.Smooth R S] [Algebra.Smooth R T]
    [Algebra.FinitePresentation S T]
    (hmap : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Bijective
      (((KaehlerDifferential.mapBaseChange R S T).baseChange
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))).dualMap)) :
    Algebra.Etale S T := by
  have hbijective : Function.Bijective (KaehlerDifferential.mapBaseChange R S T) := by
    apply linearMap_bijective_of_fibers
    intro ideal hmaximal
    exact LinearMap.dualMap_bijective_iff.mp (hmap ideal)
  have : Algebra.FormallyEtale S T :=
    formallyEtale_of_bijective_map R S T hbijective
  exact {}

section Modules

variable {A M N P : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

private theorem localizedMap_baseChange (f : M →ₗ[A] N)
    (ideal : Ideal A) [ideal.IsPrime] :
    IsLocalizedModule.map ideal.primeCompl
      (TensorProduct.mk A (Localization.AtPrime ideal) M 1)
      (TensorProduct.mk A (Localization.AtPrime ideal) N 1) f =
      (f.baseChange (Localization.AtPrime ideal)).restrictScalars A := by
  apply IsLocalizedModule.linearMap_ext ideal.primeCompl
    (TensorProduct.mk A (Localization.AtPrime ideal) M 1)
    (TensorProduct.mk A (Localization.AtPrime ideal) N 1)
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [IsLocalizedModule.map_apply]
  change (1 : Localization.AtPrime ideal) ⊗ₜ[A] f x =
    (f.baseChange (Localization.AtPrime ideal)) (1 ⊗ₜ[A] x)
  rw [LinearMap.baseChange_tmul]

private theorem local_fiber_injective (f : M →ₗ[A] N)
    (ideal : Ideal A) [ideal.IsMaximal]
    (hmap : Function.Injective
      (f.baseChange (IsLocalRing.ResidueField (Localization.AtPrime ideal)))) :
    Function.Injective ((f.baseChange (Localization.AtPrime ideal)).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime ideal))) := by
  change Function.Injective ((f.baseChange (Localization.AtPrime ideal)).baseChange
    (IsLocalRing.ResidueField (Localization.AtPrime ideal)))
  rw [LinearMap.baseChange_baseChange]
  simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp] using hmap

variable [Module.Finite A M] [Module.Finite A N] [Module.Flat A N]

/-- Injectivity from a finite module into a finite flat module can be checked on residue fields. -/
theorem linearMap_injective_of_fibers (f : M →ₗ[A] N)
    (hmap : ∀ (ideal : Ideal A) [ideal.IsMaximal], Function.Injective
      (f.baseChange (IsLocalRing.ResidueField (Localization.AtPrime ideal)))) :
    Function.Injective f := by
  apply injective_of_isLocalized_maximal
    (fun ideal _ => Localization.AtPrime ideal ⊗[A] M)
    (fun ideal _ => TensorProduct.mk A (Localization.AtPrime ideal) M 1)
    (fun ideal _ => Localization.AtPrime ideal ⊗[A] N)
    (fun ideal _ => TensorProduct.mk A (Localization.AtPrime ideal) N 1) f
  intro ideal hmaximal
  rw [localizedMap_baseChange f ideal]
  change Function.Injective (f.baseChange (Localization.AtPrime ideal))
  have : Module.Free (Localization.AtPrime ideal)
      (Localization.AtPrime ideal ⊗[A] N) := Module.free_of_flat_of_isLocalRing
  obtain ⟨g, hg⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective
      (f.baseChange (Localization.AtPrime ideal))).mpr
        (local_fiber_injective f ideal (hmap ideal))
  exact (show Function.LeftInverse g (f.baseChange (Localization.AtPrime ideal)) from
    fun x => LinearMap.congr_fun hg x).injective

/-- A finitely presented cokernel with finite source and finite flat middle term is projective
if the first map is injective on every maximal residue field. -/
theorem projective_of_injective_fibers [Module.FinitePresentation A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P) (hexact : Function.Exact f g)
    (hsurj : Function.Surjective g)
    (hmap : ∀ (ideal : Ideal A) [ideal.IsMaximal], Function.Injective
      (f.baseChange (IsLocalRing.ResidueField (Localization.AtPrime ideal)))) :
    Module.Projective A P := by
  apply Module.projective_of_localization_maximal'
    (fun ideal _ => Localization.AtPrime ideal)
    (fun ideal _ => Localization.AtPrime ideal ⊗[A] P)
    (fun ideal _ => TensorProduct.mk A (Localization.AtPrime ideal) P 1)
  intro ideal hmaximal
  have : Module.Free (Localization.AtPrime ideal)
      (Localization.AtPrime ideal ⊗[A] N) := Module.free_of_flat_of_isLocalRing
  have : Module.Free (Localization.AtPrime ideal)
      (Localization.AtPrime ideal ⊗[A] P) :=
    Module.free_of_lTensor_residueField_injective
      (f.baseChange (Localization.AtPrime ideal)) (g.baseChange (Localization.AtPrime ideal))
      (g.baseChange_surjective _ hsurj)
      (lTensor_exact (Localization.AtPrime ideal) hexact hsurj)
      (local_fiber_injective f ideal (hmap ideal))
  infer_instance

end Modules

section Algebras

/-- Injectivity of the differential map kills relative first cotangent homology if the
first cotangent homology over the base ring vanishes. -/
theorem h1Cotangent_of_injective_map
    [Subsingleton (Algebra.H1Cotangent R T)]
    (hmap : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton (Algebra.H1Cotangent S T) := by
  have hdelta (x : Algebra.H1Cotangent S T) : Algebra.H1Cotangent.δ R S T x = 0 := by
    apply hmap
    rw [map_zero]
    exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
  have hcotangent (x : Algebra.H1Cotangent S T) : x = 0 := by
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hdelta x)
    calc
      x = Algebra.H1Cotangent.map R S T T y := hy.symm
      _ = Algebra.H1Cotangent.map R S T T 0 := congrArg _ (Subsingleton.elim y 0)
      _ = 0 := map_zero _
  exact ⟨fun x y => (hcotangent x).trans (hcotangent y).symm⟩

/-- Surjective dual differential maps make a finitely presented morphism between smooth
algebras smooth. -/
theorem smooth_of_surjective_dual_map [Algebra.Smooth R S] [Algebra.Smooth R T]
    [Algebra.FinitePresentation S T]
    (hmap : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Surjective
      (((KaehlerDifferential.mapBaseChange R S T).baseChange
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))).dualMap)) :
    Algebra.Smooth S T := by
  have hfibers : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Injective
      ((KaehlerDifferential.mapBaseChange R S T).baseChange
        (IsLocalRing.ResidueField (Localization.AtPrime ideal))) := by
    intro ideal hmaximal
    exact LinearMap.dualMap_surjective_iff.mp (hmap ideal)
  have : Module.FinitePresentation T Ω[T⁄S] :=
    Module.finitePresentation_of_surjective (KaehlerDifferential.map R S T T)
      (KaehlerDifferential.map_surjective R S T) (by
        rw [(KaehlerDifferential.exact_mapBaseChange_map R S T).linearMap_ker_eq]
        simpa only [Submodule.map_top] using
          (Module.Finite.fg_top (R := T) (M := T ⊗[S] Ω[S⁄R])).map
            (KaehlerDifferential.mapBaseChange R S T))
  have : Module.Projective T Ω[T⁄S] := projective_of_injective_fibers
    (KaehlerDifferential.mapBaseChange R S T) (KaehlerDifferential.map R S T T)
    (KaehlerDifferential.exact_mapBaseChange_map R S T)
    (KaehlerDifferential.map_surjective R S T) hfibers
  have : Subsingleton (Algebra.H1Cotangent S T) :=
    h1Cotangent_of_injective_map R S T (linearMap_injective_of_fibers _ hfibers)
  have : Algebra.FormallySmooth S T := ⟨inferInstance, inferInstance⟩
  exact {}

end Algebras



end GroupActions
