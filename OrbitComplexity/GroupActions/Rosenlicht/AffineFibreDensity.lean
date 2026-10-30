import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import Mathlib.RingTheory.Noetherian.Basic
import OrbitComplexity.GroupActions.Rosenlicht.FibreDensityAlgebra

/-!
# Generic fibre density over affine varieties
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

/-- A nonempty open subset of an integral affine variety is dense in every
fibre over a nonempty open subset of an integral affine base variety. -/
theorem exists_open_dense_fibres_affine {K : Type u} [Field K]
    (Y X : GroupActions.Variety K) [IrreducibleSpace Y.scheme]
    [IrreducibleSpace X.scheme] [IsAffine Y.scheme] [IsAffine X.scheme]
    (f : Y.toOver ⟶ X.toOver) (U : Y.scheme.Opens) (hU : (U : Set Y.scheme).Nonempty) :
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧ ∀ x ∈ V,
      Dense {z : f.left ⁻¹' {x} | z.val ∈ U} := by
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  let g : Y.scheme ⟶ X.scheme := f.left
  let R := Γ(X.scheme, ⊤)
  let B := Γ(Y.scheme, ⊤)
  obtain ⟨φR, hR⟩ := Spec.map_surjective (X.scheme.isoSpec.inv ≫ X.toSpec)
  obtain ⟨φB, hB⟩ := Spec.map_surjective (Y.scheme.isoSpec.inv ≫ Y.toSpec)
  let : Algebra K R := φR.hom.toAlgebra
  let : Algebra K B := φB.hom.toAlgebra
  let : Algebra R B := g.appTop.hom.toAlgebra
  have hcomm : φB = φR ≫ g.appTop := by
    apply Spec.map_injective
    rw [Spec.map_comp, hB, hR, ← Category.assoc, Scheme.isoSpec_inv_naturality,
      Category.assoc]
    exact congrArg (fun h ↦ Y.scheme.isoSpec.inv ≫ h)
      (show Y.toSpec = g ≫ X.toSpec from f.w.symm)
  have : IsScalarTower K R B := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hcomm)
  have hftR : LocallyOfFiniteType (Spec.map φR) := by rw [hR]; infer_instance
  have hftB : LocallyOfFiniteType (Spec.map φB) := by rw [hB]; infer_instance
  have : Algebra.FiniteType K R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φR)).mp hftR
  have : Algebra.FiniteType K B :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φB)).mp hftB
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have : Algebra.FiniteType R B := Algebra.FiniteType.of_restrictScalars_finiteType K R B
  have hηU : genericPoint Y.scheme ∈ U :=
    ((genericPoint_spec Y.scheme).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  obtain ⟨b, hbU, hηb⟩ := (isAffineOpen_top Y.scheme).exists_basicOpen_le
    ⟨genericPoint Y.scheme, hηU⟩ (show genericPoint Y.scheme ∈ (⊤ : Y.scheme.Opens) from trivial)
  have hb : b ≠ 0 := by
    intro hb
    simp [hb] at hηb
  obtain ⟨d, hd, hdense⟩ := exists_basicOpen_dense_fibres R B b hb
  let V : X.scheme.Opens := X.scheme.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen d
  refine ⟨V, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := X.scheme.isoSpec.hom.homeomorph.surjective
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
    refine ⟨x, ?_⟩
    change X.scheme.isoSpec.hom.homeomorph x ∈ PrimeSpectrum.basicOpen d
    rw [hx]
    exact (PrimeSpectrum.mem_basicOpen d ⟨⊥, inferInstance⟩).mpr hd
  · intro x hx
    let e : (f.left ⁻¹' {x}) ≃ₜ
        (PrimeSpectrum.comap (algebraMap R B) ⁻¹' {X.scheme.isoSpec.hom x}) :=
      Y.scheme.isoSpec.hom.homeomorph.subtype (by
        intro y
        change f.left y = x ↔
          (Spec.map g.appTop) (Y.scheme.isoSpec.hom y) = X.scheme.isoSpec.hom x
        have hc : (Spec.map g.appTop) (Y.scheme.isoSpec.hom y) =
            X.scheme.isoSpec.hom (f.left y) :=
          congrArg (fun m : Y.scheme ⟶ Spec (.of R) ↦ m y)
            (Scheme.isoSpec_hom_naturality g)
        rw [hc]
        exact X.scheme.isoSpec.hom.homeomorph.injective.eq_iff.symm)
    have hD := hdense (X.scheme.isoSpec.hom x) hx
    have hi := e.symm.surjective.denseRange.dense_image e.symm.continuous hD
    apply hi.mono
    rintro z ⟨q, hq, rfl⟩
    apply hbU
    rw [← Scheme.map_PrimeSpectrum_basicOpen_of_affine Y.scheme b]
    change (e (e.symm q)).val ∈ PrimeSpectrum.basicOpen b
    rw [e.apply_symm_apply]
    exact hq

end

end GroupActions.Variety
