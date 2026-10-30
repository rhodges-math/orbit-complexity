import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ModelImages
import OrbitComplexity.FrobeniusSplitting.Normality.GraphElements
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Restricting a original contraction to its specified arithmetic image model

-/

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

section InjectiveFactor

variable {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R D]

/-- Factor a specified algebra map through a specified injective map. -/
def retainedFactor (f : B →ₐ[R] D) (hf : Function.Injective f)
    (g : A →ₐ[R] D) (h : ∀ a, g a ∈ f.range) : A →ₐ[R] B :=
  (AlgEquiv.ofInjective f hf).symm.toAlgHom.comp (g.codRestrict f.range h)

/-- The injective factor retains the original algebra map pointwise. -/
theorem retainedFactor_apply (f : B →ₐ[R] D) (hf : Function.Injective f)
    (g : A →ₐ[R] D) (h : ∀ a, g a ∈ f.range) (a : A) :
    f (retainedFactor f hf g h a) = g a := by
  have he := congrArg Subtype.val
    ((AlgEquiv.ofInjective f hf).apply_symm_apply (g.codRestrict f.range h a))
  simpa only [retainedFactor, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgEquiv.ofInjective_apply, AlgHom.coe_codRestrict] using he

end InjectiveFactor

section Restricted

variable {R K C : Type u} [CommRing R] [CommRing K] [CommRing C]
    [Algebra R K] [Algebra K C] [Algebra R C] [IsScalarTower R K C]

/-- Restrict the given original polynomial map to a preserved image subalgebra. -/
def retainedPolynomial (D : Subalgebra R C) (σ : C →ₐ[K] Polynomial C)
    (hσ : ∀ d : D, σ (d : C) ∈ (Polynomial.mapAlgHom D.val).range) :
    D →ₐ[R] Polynomial D :=
  retainedFactor (Polynomial.mapAlgHom D.val)
    (Polynomial.map_injective D.val.toRingHom Subtype.val_injective)
    ((σ.restrictScalars R).comp D.val) hσ

/-- Restriction retains the exact original polynomial coordinate values. -/
theorem retainedPolynomial_apply (D : Subalgebra R C) (σ : C →ₐ[K] Polynomial C)
    (hσ : ∀ d : D, σ (d : C) ∈ (Polynomial.mapAlgHom D.val).range) (d : D) :
    Polynomial.map D.val.toRingHom (retainedPolynomial D σ hσ d) = σ (d : C) := by
  have h := retainedFactor_apply (Polynomial.mapAlgHom D.val)
    (Polynomial.map_injective D.val.toRingHom Subtype.val_injective)
    ((σ.restrictScalars R).comp D.val) hσ d
  simpa only [retainedPolynomial, Polynomial.coe_mapAlgHom, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Subalgebra.val_apply, AlgHom.toRingHom_eq_coe] using h

/-- Restrict the original scalar origin through the injective coefficient map. -/
def retainedOrigin (D : Subalgebra R C) (ε : C →ₐ[K] K)
    (hR : Function.Injective (algebraMap R K))
    (hε : ∀ d : D, ε (d : C) ∈ (Algebra.ofId R K).range) : D →ₐ[R] R :=
  retainedFactor (Algebra.ofId R K) hR ((ε.restrictScalars R).comp D.val) hε

/-- Restriction retains the exact original scalar origin. -/
theorem retainedOrigin_apply (D : Subalgebra R C) (ε : C →ₐ[K] K)
    (hR : Function.Injective (algebraMap R K))
    (hε : ∀ d : D, ε (d : C) ∈ (Algebra.ofId R K).range) (d : D) :
    algebraMap R K (retainedOrigin D ε hR hε d) = ε (d : C) := by
  have h := retainedFactor_apply (Algebra.ofId R K) hR
    ((ε.restrictScalars R).comp D.val) hε d
  simpa only [retainedOrigin, Algebra.ofId_apply, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Subalgebra.val_apply] using h

/-- The identity endpoint is reflected through the original image inclusion. -/
theorem retainedPolynomial_one (D : Subalgebra R C) (σ : C →ₐ[K] Polynomial C)
    (hσ : ∀ d : D, σ (d : C) ∈ (Polynomial.mapAlgHom D.val).range)
    (hOne : ∀ c : C, (σ c).eval 1 = c) (d : D) :
    (retainedPolynomial D σ hσ d).eval 1 = d := by
  apply Subtype.val_injective
  have he : (Polynomial.map D.val.toRingHom (retainedPolynomial D σ hσ d)).eval 1 =
      ((retainedPolynomial D σ hσ d).eval 1 : D) := by
    simpa only [map_one, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Subalgebra.val_apply] using
      (Polynomial.eval_map_apply (f := D.val.toRingHom)
        (p := retainedPolynomial D σ hσ d) (1 : D))
  rw [retainedPolynomial_apply, hOne] at he
  exact he.symm

/-- The scalar zero endpoint is reflected through the same image inclusion. -/
theorem retainedPolynomial_zero (D : Subalgebra R C) (σ : C →ₐ[K] Polynomial C)
    (ε : C →ₐ[K] K)
    (hσ : ∀ d : D, σ (d : C) ∈ (Polynomial.mapAlgHom D.val).range)
    (hR : Function.Injective (algebraMap R K))
    (hε : ∀ d : D, ε (d : C) ∈ (Algebra.ofId R K).range)
    (hZero : ∀ c : C, (σ c).eval 0 = algebraMap K C (ε c)) (d : D) :
    (retainedPolynomial D σ hσ d).eval 0 =
      algebraMap R D (retainedOrigin D ε hR hε d) := by
  apply Subtype.val_injective
  have he : (Polynomial.map D.val.toRingHom (retainedPolynomial D σ hσ d)).eval 0 =
      ((retainedPolynomial D σ hσ d).eval 0 : D) := by
    simpa only [map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Subalgebra.val_apply] using
      (Polynomial.eval_map_apply (f := D.val.toRingHom)
        (p := retainedPolynomial D σ hσ d) (0 : D))
  calc
    (((retainedPolynomial D σ hσ d).eval 0 : D) : C) =
        (Polynomial.map D.val.toRingHom (retainedPolynomial D σ hσ d)).eval 0 := he.symm
    _ = (σ (d : C)).eval 0 :=
      congrArg (fun p : Polynomial C => p.eval 0) (retainedPolynomial_apply D σ hσ d)
    _ = algebraMap K C (ε (d : C)) := hZero (d : C)
    _ = algebraMap K C (algebraMap R K (retainedOrigin D ε hR hε d)) :=
      congrArg (algebraMap K C) (retainedOrigin_apply D ε hR hε d).symm
    _ = algebraMap R C (retainedOrigin D ε hR hε d) :=
      (IsScalarTower.algebraMap_apply R K C _).symm
    _ = ((algebraMap R D (retainedOrigin D ε hR hε d) : D) : C) :=
      (D.val.commutes _).symm

/-- Preservation on a set of algebra generators gives preservation on its
whole generated subalgebra, for the same original polynomial map. -/
theorem retainedPolynomial_range {ι : Type*} (D : Subalgebra R C)
    (x : ι → C) (hD : D = Algebra.adjoin R (Set.range x))
    (σ : C →ₐ[K] Polynomial C)
    (hc : ∀ i n, (σ (x i)).coeff n ∈ D) :
    ∀ d : D, σ (d : C) ∈ (Polynomial.mapAlgHom D.val).range := by
  have hgen : ∀ i, σ (x i) ∈ (Polynomial.mapAlgHom D.val).range := by
    intro i
    have hl : σ (x i) ∈ Polynomial.lifts D.val.toRingHom :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr
        (fun n => ⟨⟨(σ (x i)).coeff n, hc i n⟩, rfl⟩)
    obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).mp hl
    exact ⟨p, hp⟩
  let T : Subalgebra R C := ((Polynomial.mapAlgHom D.val).range).comap
    (σ.restrictScalars R)
  have hle : D ≤ T := by
    rw [hD]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hgen i
  exact fun d => hle d.property

/-- Scalar preservation on the same generators gives preservation of the
original origin on the whole generated subalgebra. -/
theorem retainedOrigin_range {ι : Type*} (D : Subalgebra R C)
    (x : ι → C) (hD : D = Algebra.adjoin R (Set.range x))
    (ε : C →ₐ[K] K) (hc : ∀ i, ε (x i) ∈ (Algebra.ofId R K).range) :
    ∀ d : D, ε (d : C) ∈ (Algebra.ofId R K).range := by
  let T : Subalgebra R C := (Algebra.ofId R K).range.comap (ε.restrictScalars R)
  have hle : D ≤ T := by
    rw [hD]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hc i
  exact fun d => hle d.property

end Restricted


/-- a specified affine arithmetic image model retaining the original polynomial
family, scalar origin, tensor comparison and both endpoint equations. -/
structure ArithmeticContractionModel
    {R K C : Type u} [CommRing R] [CommRing K] [CommRing C]
    [Algebra R K] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
    (σ : C →ₐ[K] Polynomial C) (ε : C →ₐ[K] K) where
  /-- The arithmetic algebra is a specified subalgebra of the original algebra. -/
  model : Subalgebra R C
  /-- The arithmetic algebra is finitely presented over its coefficient ring. -/
  finitePresentation : Algebra.FinitePresentation R model
  /-- Scalar extension identifies this image model with the original algebra. -/
  comparison : K ⊗[R] model ≃ₐ[K] C
  /-- The comparison retains the original inclusion on pure tensors. -/
  comparison_tmul : ∀ (k : K) (c : model),
    comparison (k ⊗ₜ[R] c) = algebraMap K C k * (c : C)
  /-- The polynomial family on this same arithmetic image. -/
  family : model →ₐ[R] Polynomial model
  /-- The scalar origin on this same arithmetic image. -/
  origin : model →ₐ[R] R
  /-- Polynomial coordinates agree with the specified original family. -/
  family_native : ∀ c : model, Polynomial.map model.val.toRingHom (family c) = σ (c : C)
  /-- The origin agrees with the specified original scalar origin. -/
  origin_native : ∀ c : model, algebraMap R K (origin c) = ε (c : C)
  /-- The arithmetic family has its identity endpoint. -/
  one : ∀ c : model, (family c).eval 1 = c
  /-- The arithmetic family has its original scalar endpoint. -/
  zero : ∀ c : model, (family c).eval 0 = algebraMap R model (origin c)

/-- Finitely many original polynomial contractions have simultaneous specified
finitely presented image models over one enlarged finitely generated integer
subalgebra. Their original tensor comparisons and endpoint values are retained. -/
theorem exists_contraction_models
    {I : Type*} [Finite I] {K : Type u} [CommRing K]
    (C : I → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra K (C i)]
    (vars rels : I → Type*) [∀ i, Finite (vars i)] [∀ i, Finite (rels i)]
    (P : ∀ i, Algebra.Presentation K (C i) (vars i) (rels i))
    (σ : ∀ i, C i →ₐ[K] Polynomial (C i)) (ε : ∀ i, C i →ₐ[K] K)
    (hOne : ∀ i c, (σ i c).eval 1 = c)
    (hZero : ∀ i c, (σ i c).eval 0 = algebraMap K (C i) (ε i c))
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ R : Subalgebra ℤ K, S ≤ R ∧ R.FG ∧
      Nonempty (∀ i, ArithmeticContractionModel (R := R) (σ i) (ε i)) := by
  classical
  let scalars : Set K := ⋃ i, Set.range (fun j : vars i => ε i ((P i).val j))
  have hscalars : scalars.Finite := Set.finite_iUnion fun i => Set.finite_range _
  let T : Subalgebra ℤ K := S ⊔ Algebra.adjoin ℤ scalars
  have hT : T.FG := hS.sup (Subalgebra.fg_def.mpr ⟨scalars, hscalars, rfl⟩)
  let L (i : I) := Σ j : vars i, (σ i ((P i).val j)).support
  let element (i : I) (z : L i) : C i := (σ i ((P i).val z.1)).coeff z.2.val
  obtain ⟨R, hP, _, hTR, hfg, hfp, _, hcapture⟩ :=
    exists_arithmetic_graph_elements (I := I) (J := Empty) T hT C vars rels P
      (fun e : Empty => nomatch e) (fun e : Empty => nomatch e)
      (fun e : Empty => nomatch e) L element
  let (i : I) : (P i).HasCoeffs R := hP i
  let : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hfg
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  refine ⟨R, (show S ≤ T from le_sup_left).trans hTR, hfg, ⟨fun i => ?_⟩⟩
  let e := (P i).tensorModelOfHasCoeffsEquiv R
  let D : Subalgebra R (C i) := (tensorImageHom e).range
  let : Algebra.FinitePresentation R ((P i).ModelOfHasCoeffs R) := hfp i
  have hD : D = Algebra.adjoin R (Set.range (P i).val) :=
    tensorImageHom_range (P i)
  have hcoeff (j : vars i) (n : ℕ) : (σ i ((P i).val j)).coeff n ∈ D := by
    by_cases hn : n ∈ (σ i ((P i).val j)).support
    · obtain ⟨m, hm⟩ := hcapture i ⟨j, ⟨n, hn⟩⟩
      refine ⟨m, ?_⟩
      exact (tensorImageHom_apply e m).trans hm
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact D.zero_mem
  have hσ : ∀ d : D, σ i (d : C i) ∈ (Polynomial.mapAlgHom D.val).range :=
    retainedPolynomial_range D (P i).val hD (σ i) hcoeff
  have hscalar (j : vars i) :
      ε i ((P i).val j) ∈ (Algebra.ofId R K).range := by
    refine ⟨⟨ε i ((P i).val j), ?_⟩, rfl⟩
    apply hTR
    apply (show Algebra.adjoin ℤ scalars ≤ T from le_sup_right)
    apply Algebra.subset_adjoin
    exact Set.mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩
  have hε : ∀ d : D, ε i (d : C i) ∈ (Algebra.ofId R K).range :=
    retainedOrigin_range D (P i).val hD (ε i) hscalar
  have hR : Function.Injective (algebraMap R K) := Subtype.val_injective
  exact
    { model := D
      finitePresentation := tensorImage_finitePresentation e
      comparison := tensorImageEquiv e
      comparison_tmul := tensorImageEquiv_tmul e
      family := retainedPolynomial D (σ i) hσ
      origin := retainedOrigin D (ε i) hR hε
      family_native := retainedPolynomial_apply D (σ i) hσ
      origin_native := retainedOrigin_apply D (ε i) hR hε
      one := retainedPolynomial_one D (σ i) hσ (hOne i)
      zero := retainedPolynomial_zero D (σ i) (ε i) hσ hR hε (hZero i) }

end FrobeniusSplitting
