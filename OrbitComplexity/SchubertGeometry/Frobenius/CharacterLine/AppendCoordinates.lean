import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendMatching
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.CoefficientCharts
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AppendChart
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialBridge
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport

/-! # Polynomial coordinates of the specified projective append chart -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine

open private CoframeTransport.algebraMapOver CoframeTransport.algebraMapOver_comp from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private simpleFibre fibreChart from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendMatching
open private leftMap rightMap from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
open private projectiveLinePolynomial_coeff from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.CoefficientCharts

private theorem inverse_trans_comp {C : Type v} [Category.{w} C] {X Y Z : C}
    (e : X ≅ Y) (f : Y ≅ Z) : (e ≪≫ f).inv ≫ e.hom = f.inv := by
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverse_comp {C : Type v} [Category.{w} C] {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) (c : X ⟶ Z) :
    a ≫ (b ≫ c) = c :=
  (Category.assoc a b c).symm.trans
    ((congrArg (fun f => f ≫ c) h).trans (Category.id_comp c))

private theorem outer_replace {C : Type v} [Category.{w} C] {A B D E T : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : B ⟶ E) (p : E ⟶ T)
    (h : b ≫ c = d) : ((a ≫ b) ≫ c) ≫ p = a ≫ d ≫ p :=
  (congrArg (fun f => f ≫ p) ((Category.assoc a b c).trans
    (congrArg (fun f => a ≫ f) h))).trans (Category.assoc a d p)

private theorem pairIso_fst {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {A B D X : C} (a : X ⟶ A) (b : X ⟶ B) (e : B ≅ D) :
    (lift a b ≫ (tensorIso (Iso.refl A) e).hom) ≫ fst A D = a := by
  change (lift a b ≫ (𝟙 A ⊗ₘ e.hom)) ≫ fst A D = a
  simp only [Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]

private theorem pairIso_snd {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {A B D X : C} (a : X ⟶ A) (b : X ⟶ B) (e : B ≅ D) :
    (lift a b ≫ (tensorIso (Iso.refl A) e).hom) ≫ snd A D = b ≫ e.hom := by
  change (lift a b ≫ (𝟙 A ⊗ₘ e.hom)) ≫ snd A D = b ≫ e.hom
  simp only [Category.assoc, tensorHom_snd, lift_snd_assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private def polynomialGa :
    (affineVariety K (Polynomial K)).toOver ⟶ (additiveVariety K).toOver :=
  affineMorphism (gaPolynomialEquiv K).toAlgHom

omit [IsAlgClosed K] [CharZero K] in
private theorem polynomialGa_inverse :
    (polynomialGa (K := K)).left ≫
        Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) =
      𝟙 (Spec (.of (Polynomial K))) :=
  (Scheme.Spec.mapIso (gaPolynomialEquiv K).toRingEquiv.toCommRingCatIso.op).hom_inv_id

omit [IsAlgClosed K] [CharZero K] in
private abbrev coefficientBase (A : CommAlgCat.{u} K) : Over (Spec (.of K)) :=
  (algSpec (.of K)).obj (.op A)
omit [IsAlgClosed K] [CharZero K] in
private abbrev polynomialBase (A : CommAlgCat.{u} K) : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial A))))

omit [IsAlgClosed K] [CharZero K] in
private def baseParameter (A : CommAlgCat.{u} K) :
    polynomialBase A ⟶ coefficientBase A :=
  CoframeTransport.algebraMapOver (IsScalarTower.toAlgHom K A (Polynomial A))

omit [IsAlgClosed K] [CharZero K] in
private def polynomialCoefficient (A : CommAlgCat.{u} K) :
    polynomialBase A ⟶
      (affineVariety K (Polynomial K)).toOver :=
  CoframeTransport.algebraMapOver (Polynomial.mapAlgHom (Algebra.ofId K A))

omit [IsAlgClosed K] [CharZero K] in
private def polynomialParameter (A : CommAlgCat.{u} K) :
    polynomialBase A ⟶ (additiveVariety K).toOver :=
  polynomialCoefficient A ≫ polynomialGa (K := K)

omit [IsAlgClosed K] [CharZero K] in
private theorem polynomialCoefficient_left (A : CommAlgCat.{u} K) :
    (polynomialCoefficient A).left =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K A))) := rfl

private theorem fibreChart_iso (i : G.rootBase.support) (j : Fin 2) :
    fibreChart G i j ≫ (simpleSchubertIso G i).hom = projectiveLineChart K ⟨j⟩ := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact simpleSchubertIso_positive G i
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact simpleSchubertIso_negative G i

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: polynomialParameter_chart"

omit [IsAlgClosed K] [CharZero K] in
private theorem polynomialParameter_chart (A : CommAlgCat.{u} K) (j : ULift.{u} (Fin 2)) :
    (polynomialParameter A).left ≫ (projectiveLineChart K j).left =
      projectiveLinePolynomialChart A j ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A) := by
  have hfield : (polynomialGa (K := K)).left ≫ (projectiveLineChart K j).left =
      projectiveLinePolynomialChart K j :=
    (congrArg (fun f => (polynomialGa (K := K)).left ≫ f)
      (ProjectiveLine.projectiveChart_polynomial K j)).trans
        (inverse_comp _ _ (polynomialGa_inverse (K := K)) _)
  have hfirst := (Category.assoc (polynomialCoefficient A).left
    (polynomialGa (K := K)).left (projectiveLineChart K j).left).trans
      (congrArg (fun f => (polynomialCoefficient A).left ≫ f) hfield)
  have hsecond := congrArg (fun f => f ≫ projectiveLinePolynomialChart K j)
    (polynomialCoefficient_left A)
  exact hfirst.trans (hsecond.trans
    (projectiveLinePolynomial_coeff K A (algebraMap K A) j).symm)

private def polynomialPair (i : G.rootBase.support) (A : CommAlgCat.{u} K) (j : Fin 2) :
    polynomialBase A ⟶ coefficientBase A ⊗ (simpleFibre G i).toOver :=
  lift (baseParameter A) (polynomialParameter A ≫ fibreChart G i j)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: polynomialPair_chart"

private theorem polynomialPair_chart (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (j : Fin 2) :
    projectiveLinePolynomialChart A ⟨j⟩ ≫ (simpleBorelLineIso G i A).inv =
      (polynomialPair G i A j).left := by
  let E := (Over.forget (Spec (.of K))).mapIso
    (tensorIso (Iso.refl (coefficientBase A)) (simpleSchubertIso G i))
  let B := projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)
  let _ : IsIso E.hom := E.isIso_hom
  have hi : (simpleBorelLineIso G i A).inv ≫ E.hom = B.hom :=
    inverse_trans_comp E B.symm
  have hfst := congrArg (fun f : polynomialBase A ⟶ coefficientBase A => f.left)
    (pairIso_fst (baseParameter A) (polynomialParameter A ≫ fibreChart G i j)
      (simpleSchubertIso G i))
  have hsnd := congrArg (fun f : polynomialBase A ⟶
      Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))) => f.left)
    (pairIso_snd (baseParameter A) (polynomialParameter A ≫ fibreChart G i j)
      (simpleSchubertIso G i))
  have hb : projectiveLinePolynomialChart A ⟨j⟩ ≫
      projectiveToSpec A (ULift.{u} (Fin 2)) = (baseParameter A).left :=
    projectiveLinePolynomialChart_base A ⟨j⟩
  have hp : projectiveLinePolynomialChart A ⟨j⟩ ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A) =
        (polynomialParameter A).left ≫ (projectiveLineChart K ⟨j⟩).left :=
    (polynomialParameter_chart A ⟨j⟩).symm
  have hs : (polynomialParameter A).left ≫ (projectiveLineChart K ⟨j⟩).left =
      (polynomialPair G i A j).left ≫ E.hom ≫ pullback.snd _ _ :=
    (congrArg (fun f : polynomialBase A ⟶
      Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))) => f.left)
      (congrArg (fun f => polynomialParameter A ≫ f) (fibreChart_iso G i j))).symm.trans
        ((congrArg (fun f : polynomialBase A ⟶
          Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))) => f.left)
          (Category.assoc (polynomialParameter A) (fibreChart G i j)
            (simpleSchubertIso G i).hom)).symm.trans hsnd.symm)
  apply (cancel_mono E.hom).mp
  apply pullback.hom_ext
  · exact (outer_replace _ _ _ _ _ hi).trans
      ((congrArg (fun f => projectiveLinePolynomialChart A ⟨j⟩ ≫ f)
        (projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap K A))).trans
          (hb.trans hfst.symm))
  · exact (outer_replace _ _ _ _ _ hi).trans
      ((congrArg (fun f => projectiveLinePolynomialChart A ⟨j⟩ ≫ f)
        (projectiveBaseChange_snd (ULift.{u} (Fin 2)) (algebraMap K A))).trans
          (hp.trans hs))

omit [IsAlgClosed K] [CharZero K] in
private abbrev laurentBase (A : CommAlgCat.{u} K) : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (LaurentPolynomial A))))

omit [IsAlgClosed K] [CharZero K] in
private def leftParameter (A : CommAlgCat.{u} K) : laurentBase A ⟶ polynomialBase A :=
  Over.homMk (leftMap A) (by
    exact (CoframeTransport.algebraMapOver ((Polynomial.toLaurentAlg (R := A)).restrictScalars
      K)).w)

omit [IsAlgClosed K] [CharZero K] in
private def rightParameter (A : CommAlgCat.{u} K) : laurentBase A ⟶ polynomialBase A :=
  Over.homMk (rightMap A) (by
    exact (CoframeTransport.algebraMapOver ((LaurentPolynomial.invert.toAlgHom.comp
      (Polynomial.toLaurentAlg (R := A))).restrictScalars K)).w)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: leftParameter_eq"

set_option maxHeartbeats 3000 in
omit [IsAlgClosed K] [CharZero K] in
private theorem leftParameter_eq (A : CommAlgCat.{u} K) :
    leftParameter A = CoframeTransport.algebraMapOver
      ((Polynomial.toLaurentAlg (R := A)).restrictScalars K) := by
  apply CategoryTheory.Over.OverMorphism.ext
  rfl

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: rightParameter_eq"

set_option maxHeartbeats 3000 in
omit [IsAlgClosed K] [CharZero K] in
private theorem rightParameter_eq (A : CommAlgCat.{u} K) :
    rightParameter A = CoframeTransport.algebraMapOver
      ((LaurentPolynomial.invert.toAlgHom.comp
        (Polynomial.toLaurentAlg (R := A))).restrictScalars K) := by
  apply CategoryTheory.Over.OverMorphism.ext
  rfl

omit [IsAlgClosed K] [CharZero K] in
private def laurentCoefficient (A : CommAlgCat.{u} K) :
    laurentBase A ⟶ laurentBase (CommAlgCat.of K K) :=
  CoframeTransport.algebraMapOver (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId K A))

omit [IsAlgClosed K] [CharZero K] in
private def laurentTorus (A : CommAlgCat.{u} K) :
    laurentBase A ⟶ (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver :=
  laurentCoefficient A ≫ CoframeTransport.algebraMapOver
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).symm.toAlgHom

omit [IsAlgClosed K] [CharZero K] in
private def laurentToBase (A : CommAlgCat.{u} K) : laurentBase A ⟶ coefficientBase A :=
  CoframeTransport.algebraMapOver (IsScalarTower.toAlgHom K A (LaurentPolynomial A))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: laurentPolynomialParameter"

omit [IsAlgClosed K] [CharZero K] in
private theorem laurentPolynomialParameter (A : CommAlgCat.{u} K) (n : ℤ) :
    CoframeTransport.algebraMapOver (Polynomial.aeval (R := K)
        (LaurentPolynomial.T n : LaurentPolynomial A)) ≫ polynomialGa (K := K) =
      laurentTorus A ≫ ProjectiveLine.multiplicativeParameter (K := K) n := by
  let f : Polynomial K →ₐ[K] LaurentPolynomial A := Polynomial.aeval (LaurentPolynomial.T n)
  let l : LaurentPolynomial K →ₐ[K] LaurentPolynomial A :=
    AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId K A)
  let e : MonoidAlgebra K (Multiplicative ℤ) →ₐ[K] LaurentPolynomial K :=
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).symm.toAlgHom
  let t : SymmetricAlgebra K K →ₐ[K] MonoidAlgebra K (Multiplicative ℤ) :=
    SymmetricAlgebra.lift (LinearMap.toSpanSingleton K _
      (MonoidAlgebra.single (Multiplicative.ofAdd n) (1 : K)))
  have h : f.comp (gaPolynomialEquiv K).toAlgHom = l.comp (e.comp t) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext_ring
    change f (gaPolynomialEquiv K (SymmetricAlgebra.ι K K 1)) =
      l (e (t (SymmetricAlgebra.ι K K 1)))
    rw [gaPolynomialEquiv_generator, Polynomial.aeval_X, SymmetricAlgebra.lift_ι_apply,
      LinearMap.toSpanSingleton_apply_one]
    have he : e (MonoidAlgebra.single (Multiplicative.ofAdd n) (1 : K)) =
        (LaurentPolynomial.T n : LaurentPolynomial K) := by
      apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).injective
      exact ((AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).apply_symm_apply
        (MonoidAlgebra.single (Multiplicative.ofAdd n) (1 : K))).trans
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single (R := K) n (1 : K)).symm
    have hl : l (LaurentPolynomial.T n : LaurentPolynomial K) =
        (LaurentPolynomial.T n : LaurentPolynomial A) :=
      (AddMonoidAlgebra.mapAlgHom_single (Algebra.ofId K A) n (1 : K)).trans
        (congrArg (fun a : A => AddMonoidAlgebra.single n a) (map_one (Algebra.ofId K A)))
    exact ((congrArg l he).trans hl).symm
  exact (CoframeTransport.algebraMapOver_comp (gaPolynomialEquiv K).toAlgHom f).trans
    ((congrArg CoframeTransport.algebraMapOver h).trans
      (((CoframeTransport.algebraMapOver_comp (e.comp t) l).symm.trans
        (congrArg (fun z => CoframeTransport.algebraMapOver l ≫ z)
          (CoframeTransport.algebraMapOver_comp t e).symm)).trans
            (Category.assoc (CoframeTransport.algebraMapOver l)
              (CoframeTransport.algebraMapOver e) (CoframeTransport.algebraMapOver t)).symm))

omit [IsAlgClosed K] [CharZero K] in
private theorem leftParameter_polynomial (A : CommAlgCat.{u} K) :
    leftParameter A ≫ polynomialParameter A =
      laurentTorus A ≫ ProjectiveLine.multiplicativeParameter (K := K) 1 := by
  have h : ((Polynomial.toLaurentAlg (R := A)).restrictScalars K).comp
      (Polynomial.mapAlgHom (Algebra.ofId K A)) =
      Polynomial.aeval (R := K) (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial A) := by
    ext
    simp
  have hc : leftParameter A ≫ polynomialCoefficient A =
      CoframeTransport.algebraMapOver
        (Polynomial.aeval (R := K) (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial A)) :=
    (congrArg (fun f => f ≫ polynomialCoefficient A) (leftParameter_eq A)).trans
      ((CoframeTransport.algebraMapOver_comp _ _).trans
        (congrArg CoframeTransport.algebraMapOver h))
  exact (Category.assoc (leftParameter A) (polynomialCoefficient A)
    (polynomialGa (K := K))).symm.trans
      ((congrArg (fun z => z ≫ polynomialGa (K := K)) hc).trans
        (laurentPolynomialParameter A 1))

omit [IsAlgClosed K] [CharZero K] in
private theorem rightParameter_polynomial (A : CommAlgCat.{u} K) :
    rightParameter A ≫ polynomialParameter A =
      laurentTorus A ≫ ProjectiveLine.multiplicativeParameter (K := K) (-1) := by
  have h : ((LaurentPolynomial.invert.toAlgHom.comp
      (Polynomial.toLaurentAlg (R := A))).restrictScalars K).comp
      (Polynomial.mapAlgHom (Algebra.ofId K A)) =
      Polynomial.aeval (R := K) (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial A) := by
    ext
    simp
  have hc : rightParameter A ≫ polynomialCoefficient A =
      CoframeTransport.algebraMapOver
        (Polynomial.aeval (R := K) (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial A)) :=
    (congrArg (fun f => f ≫ polynomialCoefficient A) (rightParameter_eq A)).trans
      ((CoframeTransport.algebraMapOver_comp _ _).trans
        (congrArg CoframeTransport.algebraMapOver h))
  exact (Category.assoc (rightParameter A) (polynomialCoefficient A)
    (polynomialGa (K := K))).symm.trans
      ((congrArg (fun z => z ≫ polynomialGa (K := K)) hc).trans
        (laurentPolynomialParameter A (-1)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: leftParameter_base"

set_option maxHeartbeats 3000 in
omit [IsAlgClosed K] [CharZero K] in
private theorem leftParameter_base (A : CommAlgCat.{u} K) :
    leftParameter A ≫ baseParameter A = laurentToBase A := by
  have h : ((Polynomial.toLaurentAlg (R := A)).restrictScalars K).comp
      (IsScalarTower.toAlgHom K A (Polynomial A)) =
        IsScalarTower.toAlgHom K A (LaurentPolynomial A) := by
    ext a
    simp
  exact (congrArg (fun f => f ≫ baseParameter A) (leftParameter_eq A)).trans
    ((CoframeTransport.algebraMapOver_comp _ _).trans
      (congrArg CoframeTransport.algebraMapOver h))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoordinates: rightParameter_base"

set_option maxHeartbeats 3000 in
omit [IsAlgClosed K] [CharZero K] in
private theorem rightParameter_base (A : CommAlgCat.{u} K) :
    rightParameter A ≫ baseParameter A = laurentToBase A := by
  have h : ((LaurentPolynomial.invert.toAlgHom.comp
      (Polynomial.toLaurentAlg (R := A))).restrictScalars K).comp
      (IsScalarTower.toAlgHom K A (Polynomial A)) =
        IsScalarTower.toAlgHom K A (LaurentPolynomial A) := by
    ext a
    simp
  exact (congrArg (fun f => f ≫ baseParameter A) (rightParameter_eq A)).trans
    ((CoframeTransport.algebraMapOver_comp _ _).trans
      (congrArg CoframeTransport.algebraMapOver h))


end SchubertGeometry.CharacterLine
