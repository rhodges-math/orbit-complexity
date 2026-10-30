import OrbitComplexity.FrobeniusSplitting.Normality.NilpotentFamilies
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeModels
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.TensorCancellation
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Cartesian polynomial charts under scalar comparison

A prescribed tensor comparison of coefficient rings extends to a comparison
of polynomial charts. The resulting scheme isomorphism preserves both the
coefficient projection and the original polynomial coordinate projection.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open private polynomialBaseChange polynomialBaseChange_tmul coefficientMap from
  OrbitComplexity.FrobeniusSplitting.Normality.NilpotentFamilies

open private FrobeniusSplitting.RetainedCharacter.scalarMap
  FrobeniusSplitting.RetainedCharacter.scalarMap_factor from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

namespace FrobeniusSplitting

universe u

/-- An open polynomial tensor chart in a scalar model, with coefficient
and field projections. -/
structure PolynomialOpenModel
    (S R K B A : Type u)
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [bComm : CommRing B] [aComm : CommRing A]
    [sR : Algebra S R] [sK : Algebra S K] [rK : Algebra R K]
    [sB : Algebra S B] [kA : Algebra K A] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] A) (F : Over (Spec (.of S)))
    (FK : Over (Spec (.of K))) (qF : FK.left ⟶ F.left)
    (fK : (@polynomialModel.{u} K A kComm aComm kA).left ⟶ FK.left) where
  /-- The scalar target containing the chart. -/
  flagModel : Over (Spec (.of R))
  /-- The projection to the target over the earlier coefficients. -/
  projection : flagModel.left ⟶ F.left
  /-- The target projection is a scalar-extension square. -/
  cartesian : IsPullback projection flagModel.hom F.hom
    (Spec.map (CommRingCat.ofHom (algebraMap S R)))
  /-- The field comparison of the target. -/
  fieldMap : FK.left ⟶ flagModel.left
  /-- The target field comparison is Cartesian. -/
  field_cartesian : IsPullback fieldMap FK.hom flagModel.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  /-- The field comparison respects the earlier projection. -/
  field_projection : fieldMap ≫ projection = qF
  /-- The polynomial chart map into the scalar target. -/
  map : (@polynomialModel.{u} R (R ⊗[S] B) rComm
    (inferInstanceAs (CommRing (R ⊗[S] B)))
    (inferInstanceAs (Algebra R (R ⊗[S] B)))) ⟶ flagModel
  /-- The polynomial chart map is an open immersion. -/
  openMap : IsOpenImmersion map.left
  /-- The polynomial field comparison is Cartesian. -/
  polynomial_cartesian : IsPullback
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e))))
    (@polynomialModel.{u} K A kComm aComm kA).hom
    (@polynomialModel.{u} R (R ⊗[S] B) rComm
      (inferInstanceAs (CommRing (R ⊗[S] B)))
      (inferInstanceAs (Algebra R (R ⊗[S] B)))).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  /-- The polynomial and target field comparisons commute with their maps. -/
  map_equation : fK ≫ fieldMap =
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e))) ≫ map.left

private theorem polynomial_image_eq {T R A B : Type u}
    [CommRing T] [CommRing R] [CommRing A] [CommRing B]
    [Algebra T R] [Algebra T A] [Algebra R B] [Algebra T B] [IsScalarTower T R B]
    (e : R ⊗[T] A ≃ₐ[R] B) :
    (tensorImageHom (polynomialBaseChange T R A B e)).toRingHom =
      Polynomial.mapRingHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[T] R ⊗[T] A).toRingHom) := by
  have hc : (coefficientMap T R A B e).toRingHom =
      e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[T] R ⊗[T] A).toRingHom := by
    ext a
    rfl
  apply RingHom.ext
  intro P
  change polynomialBaseChange T R A B e ((1 : R) ⊗ₜ[T] P) =
    Polynomial.map _ P
  have hm := polynomialBaseChange_tmul T R A B e 1 P
  simp only [map_one, one_mul] at hm
  change polynomialBaseChange T R A B e ((1 : R) ⊗ₜ[T] P) =
    Polynomial.map (coefficientMap T R A B e).toRingHom P at hm
  exact hm.trans (congrArg (fun f : A →+* B ↦ Polynomial.map f P) hc)

/-- A tensor comparison of coefficient rings gives the Cartesian polynomial
square and a pullback isomorphism with both specified projection equations. -/
theorem exists_scalar_polynomial_square (T R A B : Type u)
    [CommRing T] [CommRing R] [CommRing A] [CommRing B]
    [Algebra T R] [Algebra T A] [Algebra R B]
    (e : R ⊗[T] A ≃ₐ[R] B) :
    ∃ E : Spec (.of (Polynomial B)) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap T R)))
          (Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial A)))),
      E.hom ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial B))) ∧
      E.hom ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
            (e.toRingHom.comp
              (Algebra.TensorProduct.includeRight : A →ₐ[T] R ⊗[T] A).toRingHom))) ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (e.toRingHom.comp
            (Algebra.TensorProduct.includeRight : A →ₐ[T] R ⊗[T] A).toRingHom))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial B))))
        (Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial A))))
        (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  let : Algebra T B := ((algebraMap R B).comp (algebraMap T R)).toAlgebra
  let : IsScalarTower T R B := IsScalarTower.of_algebraMap_eq' rfl
  let eP : R ⊗[T] Polynomial A ≃ₐ[R] Polynomial B :=
    polynomialBaseChange T R A B e
  have hmap : (tensorImageHom eP).toRingHom =
      Polynomial.mapRingHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[T] R ⊗[T] A).toRingHom) :=
    polynomial_image_eq e
  refine ⟨affineModelIso eP, affineModelIso_fst eP, ?_, ?_⟩
  · simpa only [hmap] using affineModelIso_snd eP
  · simpa only [hmap] using (isPullback_affineModel eP).flip

private theorem coefficient_cancel
    {S R K B A : Type u}
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [bComm : CommRing B] [aComm : CommRing A]
    [sR : Algebra S R] [sK : Algebra S K] [rK : Algebra R K]
    [sB : Algebra S B] [kA : Algebra K A] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] A) (eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] A)
    (heR : eR = (@tensorCancelEquiv.{u} S R K sComm rComm kComm
      sR rK sK tower B bComm sB).trans e) :
    eR.toRingHom.comp
        (Algebra.TensorProduct.includeRight : R ⊗[S] B →ₐ[R]
          K ⊗[R] (R ⊗[S] B)).toRingHom =
      @FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e := by
  subst eR
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r b =>
      simp [tensorCancelEquiv, FrobeniusSplitting.RetainedCharacter.scalarMap,
        Algebra.smul_def]
  | add z z' hz hz' =>
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'

private theorem polynomial_spec_comp {D T A : Type u}
    [CommRing D] [CommRing T] [CommRing A] (f : D →+* T) (g : T →+* A) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (g.comp f))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply congrArg CommRingCat.ofHom
  apply RingHom.ext
  intro P
  change Polynomial.map g (Polynomial.map f P) = Polynomial.map (g.comp f) P
  rw [Polynomial.map_map]

private theorem scalar_polynomial_factor
    {S R K B A : Type u}
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [bComm : CommRing B] [aComm : CommRing A]
    [sR : Algebra S R] [sK : Algebra S K] [rK : Algebra R K]
    [sB : Algebra S B] [kA : Algebra K A] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] A) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        ((AlgEquiv.refl : R ⊗[S] B ≃ₐ[R] R ⊗[S] B).toRingHom.comp
          (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom))) =
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (e.toRingHom.comp
            (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).toRingHom))) := by
  have hu : (AlgEquiv.refl : R ⊗[S] B ≃ₐ[R] R ⊗[S] B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom =
        (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom := by
    rfl
  have hf := @FrobeniusSplitting.RetainedCharacter.scalarMap_factor S R K B A
    sComm rComm kComm bComm aComm sR sK rK sB kA tower e
    (e.toRingHom.comp (Algebra.TensorProduct.includeRight :
      B →ₐ[S] K ⊗[S] B).toRingHom) (fun _ => rfl)
  exact (polynomial_spec_comp _ _).trans
    (congrArg (fun f : B →+* A =>
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
      ((congrArg
        ((@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
          sComm rComm kComm bComm aComm sR sK rK sB kA tower e).comp ·) hu).trans hf))

/-- The polynomial projection of a scalar chart commutes with its projection
to the polynomial algebra over the coefficient model. -/
theorem polynomial_scalar_projection
    {S R K B A : Type u}
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [bComm : CommRing B] [aComm : CommRing A]
    [sR : Algebra S R] [sK : Algebra S K] [rK : Algebra R K]
    [sB : Algebra S B] [kA : Algebra K A] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] A) (Y : Scheme.{u})
    (a : Spec (.of (Polynomial A)) ⟶ Y) (q : Y ⟶ Spec (.of (Polynomial (R ⊗[S] B))))
    (ha : a ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e)))) :
    a ≫ (q ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      ((AlgEquiv.refl : R ⊗[S] B ≃ₐ[R] R ⊗[S] B).toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom)))) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).toRingHom))) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) ha).trans
      (@scalar_polynomial_factor.{u} S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e))

private theorem chart_map_compare {X H C Y B Z : Scheme.{u}}
    (m : H ⟶ C) (lC : C ⟶ Y) (bC : C ⟶ B) (lH : H ⟶ Y) (bH : H ⟶ B)
    (a : Y ⟶ Z) (β : B ⟶ Z) (hC : IsPullback lC bC a β)
    (qH : X ⟶ H) (qC : X ⟶ C)
    (hEl : m ≫ lC = lH) (hEb : m ≫ bC = bH)
    (hl : qH ≫ lH = qC ≫ lC) (hb : qH ≫ bH = qC ≫ bC) :
    qH ≫ m = qC := by
  apply hC.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (qH ≫ ·) hEl).trans hl)
  · exact (Category.assoc _ _ _).trans ((congrArg (qH ≫ ·) hEb).trans hb)


private theorem iso_projection {C : Type*} [Category C] {X Y Z W : C}
    (E : X ≅ Z) (α : Y ≅ Z) (p : Z ⟶ W) (q : Y ⟶ W) (r : X ⟶ W)
    (hα : α.hom ≫ p = q) (hE : E.hom ≫ p = r) :
    (E.hom ≫ α.inv) ≫ q = r := by
  calc
    _ = (E.hom ≫ α.inv) ≫ (α.hom ≫ p) := congrArg ((E.hom ≫ α.inv) ≫ ·) hα.symm
    _ = E.hom ≫ p := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = r := hE

/-- A map from a polynomial chart factors through its tensor scalar model,
retaining the prescribed map into the target. -/
theorem exists_polynomial_tensor_chart
    {S R K B A : Type u}
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [bComm : CommRing B] [aComm : CommRing A]
    [sR : Algebra S R] [sK : Algebra S K] [rK : Algebra R K]
    [sB : Algebra S B] [kA : Algebra K A] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] A) (CR F : Over (Spec (.of R)))
    (lC : CR.left ⟶ Spec (.of (Polynomial B)))
    (hCR : IsPullback lC CR.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial B))))
      (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (Y : Scheme.{u}) (f : Spec (.of (Polynomial A)) ⟶ Y)
    (qC : Spec (.of (Polynomial A)) ⟶ CR.left) (qF : Y ⟶ F.left)
    (it : CR ⟶ F)
    (hOldC : qC ≫ lC = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).toRingHom))))
    (hqC : qC ≫ CR.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hchart : f ≫ qF = qC ≫ it.left) :
    ∃ i : @polynomialModel.{u} R (R ⊗[S] B) rComm
      (inferInstanceAs (CommRing (R ⊗[S] B)))
      (inferInstanceAs (Algebra R (R ⊗[S] B))) ⟶ F,
      IsPullback
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
            sComm rComm kComm bComm aComm sR sK rK sB kA tower e))))
        (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial A))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[S] B)))))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      f ≫ qF = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
          sComm rComm kComm bComm aComm sR sK rK sB kA tower e))) ≫ i.left ∧
      (IsOpenImmersion it.left → IsOpenImmersion i.left) := by
  let H : Over (Spec (.of R)) := @polynomialModel.{u} R (R ⊗[S] B) rComm
      (inferInstanceAs (CommRing (R ⊗[S] B)))
      (inferInstanceAs (Algebra R (R ⊗[S] B)))
  let eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] A :=
    (@tensorCancelEquiv.{u} S R K sComm rComm kComm sR rK sK tower B bComm sB).trans e
  have hmap := @coefficient_cancel.{u} S R K B A
    sComm rComm kComm bComm aComm sR sK rK sB kA tower e eR rfl
  have hHAll := @exists_scalar_polynomial_square.{u}
    R K (R ⊗[S] B) A rComm kComm
    (inferInstanceAs (CommRing (R ⊗[S] B))) aComm rK
    (inferInstanceAs (Algebra R (R ⊗[S] B))) kA eR
  obtain ⟨_, _, _, hH⟩ := hHAll
  rw [hmap] at hH
  have hEAll := @exists_scalar_polynomial_square.{u}
    S R B (R ⊗[S] B) sComm rComm bComm
    (inferInstanceAs (CommRing (R ⊗[S] B))) sR sB
    (inferInstanceAs (Algebra R (R ⊗[S] B)))
    (AlgEquiv.refl : R ⊗[S] B ≃ₐ[R] R ⊗[S] B)
  obtain ⟨E, hEb, hEl, _⟩ := hEAll
  let α := hCR.flip.isoPullback
  let m : H.left ⟶ CR.left := E.hom ≫ α.inv
  have hmEl := iso_projection E α _ _ _ hCR.flip.isoPullback_hom_snd hEl
  have hmEb := iso_projection E α _ _ _ hCR.flip.isoPullback_hom_fst hEb
  have hfactor := @scalar_polynomial_factor.{u} S R K B A
    sComm rComm kComm bComm aComm sR sK rK sB kA tower e
  have hcompare := @chart_map_compare.{u}
    (Spec (.of (Polynomial A))) H.left CR.left (Spec (.of (Polynomial B)))
    (Spec (.of R)) (Spec (.of S)) m lC CR.hom _ H.hom
    (Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial B))))
    (Spec.map (CommRingCat.ofHom (algebraMap S R))) hCR
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e)))) qC
    hmEl hmEb (hfactor.trans hOldC.symm) (hH.w.trans hqC.symm)
  let EOver : H ⟶ CR := Over.homMk m hmEb
  refine ⟨EOver ≫ it, hH, ?_, ?_⟩
  · exact hchart.trans
      ((congrArg (· ≫ it.left) hcompare.symm).trans (Category.assoc _ _ _))
  · intro hOpen
    let : IsOpenImmersion it.left := hOpen
    let : IsIso m := by
      dsimp only [m, H, polynomialModel]
      infer_instance
    change IsOpenImmersion (m ≫ it.left)
    infer_instance

/-- Tensor cancellation gives the Cartesian coefficient square of a scalar chart. -/
theorem coefficient_scalar_cartesian
    {S R K B A : Type u}
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [bComm : CommRing B] [aComm : CommRing A]
    [sR : Algebra S R] [sK : Algebra S K] [rK : Algebra R K]
    [sB : Algebra S B] [kA : Algebra K A] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
          sComm rComm kComm bComm aComm sR sK rK sB kA tower e)))
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[S] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let rA : Algebra R A := ((algebraMap K A).comp (algebraMap R K)).toAlgebra
  let rKA : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq' rfl
  let eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] A :=
    (@tensorCancelEquiv.{u} S R K sComm rComm kComm sR rK sK tower B bComm sB).trans e
  have hmap : (@tensorImageHom R K (R ⊗[S] B) A rComm kComm
      (inferInstanceAs (CommRing (R ⊗[S] B))) aComm rK
      (inferInstanceAs (Algebra R (R ⊗[S] B))) kA rA rKA eR).toRingHom =
      @FrobeniusSplitting.RetainedCharacter.scalarMap S R K B A
        sComm rComm kComm bComm aComm sR sK rK sB kA tower e :=
    @coefficient_cancel.{u} S R K B A
      sComm rComm kComm bComm aComm sR sK rK sB kA tower e eR rfl
  have h := (@isPullback_affineModel.{u} R K (R ⊗[S] B) A
    rComm kComm (inferInstanceAs (CommRing (R ⊗[S] B))) aComm rK
    (inferInstanceAs (Algebra R (R ⊗[S] B))) kA rA rKA eR).flip
  rw [hmap] at h
  exact h

/-- Evaluation at zero commutes with a homomorphism of coefficient rings. -/
theorem polynomial_zero_map {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
      Spec.map (CommRingCat.ofHom f) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  change (Polynomial.map f P).eval 0 = f (P.eval 0)
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]

end FrobeniusSplitting
