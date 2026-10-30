import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BaseChange
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange

/-! # The coefficient morphism of the integral projective-line model -/


noncomputable section

universe u v w

namespace SchubertGeometry

section Part1

/-! # Coefficient change on polynomial charts of a projective line -/

open CategoryTheory AlgebraicGeometry GroupActions

private theorem polynomialChart_eq (R : Type u) [CommRing R]
    (j : ULift.{u} (Fin 2)) : projectiveLinePolynomialChart R j =
    Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
      {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
        projectiveChartMap R (ULift.{u} (Fin 2)) j := rfl

private theorem unique_map (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (σ : Type u) [Unique σ] :
    (MvPolynomial.uniqueAlgEquiv R σ).toRingHom.comp (MvPolynomial.map f) =
      (Polynomial.mapRingHom f).comp (MvPolynomial.uniqueAlgEquiv S σ).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro s
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.map f (MvPolynomial.C s)) =
      Polynomial.map f (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.C s))
    simp only [MvPolynomial.map_C, MvPolynomial.eval₂_C, Polynomial.map_C]
  · intro i
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.map f (MvPolynomial.X i)) =
      Polynomial.map f (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.X i))
    simp only [MvPolynomial.map_X, MvPolynomial.eval₂_X, Polynomial.map_X]

/-- The coefficient morphism acts on a polynomial chart by coefficientwise polynomial mapping. -/
private theorem projectiveLinePolynomial_coeff (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart R j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        projectiveLinePolynomialChart S j := by
  have hc : CommRingCat.ofHom (MvPolynomial.map f) ≫
      CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom =
      CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv S
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom ≫
      CommRingCat.ofHom (Polynomial.mapRingHom f) := by
    apply CommRingCat.hom_ext
    exact unique_map S R f {i : ULift.{u} (Fin 2) // i ≠ j}
  have hs := congrArg (fun h => Spec.map h) hc
  simp only [Spec.map_comp] at hs
  rw [polynomialChart_eq, polynomialChart_eq, Category.assoc, projectiveCoeffMap_chart,
    ← Category.assoc, hs, Category.assoc]

end Part1

section Part2

/-! # Affine presentation squares for the projective-line coordinate cocone -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting GroupActions

private theorem coordinate_spec (S : Type u) [CommRing S]
    (A : CommAlgCat.{u} S) (E : Over (Spec (.of S))) [IsAffine E.left]
    (e : (algSpec (.of S)).obj (.op A) ≅ E) :
    (algSpec (.of S)).map
        (CommAlgCat.ofHom (coordinateEquivOfSpecIso S A E e).symm.toAlgHom).op =
      e.hom ≫ (algΓAlgSpecAdjunction (.of S)).unit.app E := by
  have : IsIso ((algΓAlgSpecAdjunction (.of S)).unit.app E) :=
    coordinates_unit_isIso (.of S) E
  let q := e ≪≫ asIso ((algΓAlgSpecAdjunction (.of S)).unit.app E)
  change (algSpec (.of S)).map
    ((algSpec.fullyFaithful (R := CommRingCat.of S)).preimageIso q).hom = q.hom
  exact (algSpec.fullyFaithful (R := CommRingCat.of S)).map_preimage q.hom

private theorem coordinate_cancel_over (S : Type u) [CommRing S]
    (A : CommAlgCat.{u} S) (E : Over (Spec (.of S))) [IsAffine E.left]
    (e : (algSpec (.of S)).obj (.op A) ≅ E) :
    letI := coordinates_unit_isIso (.of S) E
    (algSpec (.of S)).map
        (CommAlgCat.ofHom (coordinateEquivOfSpecIso S A E e).symm.toAlgHom).op ≫
      inv ((algΓAlgSpecAdjunction (.of S)).unit.app E) = e.hom := by
  have : IsIso ((algΓAlgSpecAdjunction (.of S)).unit.app E) :=
    coordinates_unit_isIso (.of S) E
  rw [coordinate_spec, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem cocone_leg_over {S I : Type u} [CommRing S] {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of S)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
    let E := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
    letI : ∀ t, IsAffine (E.obj t).left := fun t => intersectionOpens_affine U hU t
    letI := coordinates_unit_isIso (.of S) (E.obj s)
    (intersectionCoordinateCocone f U hU).ι.app s =
      inv ((algΓAlgSpecAdjunction (.of S)).unit.app (E.obj s)) ≫
        (Over.homMk (((intersectionOpens U).obj s).ι) rfl : E.obj s ⟶ Over.mk f) := rfl

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: coordinate_cocone"; (← IO.getStderr).flush
private theorem coordinate_cocone {S I : Type u} [CommRing S] {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of S)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty}ᵒᵖ) (A : CommAlgCat.{u} S)
    (e : (algSpec (.of S)).obj (.op A) ≅
      (intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f).obj s) :
    letI : IsAffine ((intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f).obj s).left :=
      intersectionOpens_affine U hU s
    Spec.map (CommRingCat.ofHom (coordinateEquivOfSpecIso S A _ e).symm.toRingHom) ≫
      ((intersectionCoordinateCocone f U hU).ι.app s).left =
        e.hom.left ≫ ((intersectionOpens U).obj s).ι := by
  let E := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have h : IsAffine (E.obj s).left := intersectionOpens_affine U hU s
  have he : (algSpec (.of S)).map
      (CommAlgCat.ofHom (coordinateEquivOfSpecIso S A (E.obj s) e).symm.toAlgHom).op ≫
      (intersectionCoordinateCocone f U hU).ι.app s =
        e.hom ≫ (Over.homMk (((intersectionOpens U).obj s).ι) rfl :
          E.obj s ⟶ Over.mk f) := by
    rw [cocone_leg_over]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (Over.homMk (((intersectionOpens U).obj s).ι) rfl :
        E.obj s ⟶ Over.mk f)) (coordinate_cancel_over S A (E.obj s) e))
  exact congrArg (fun q => q.left) he

attribute [local instance] MvPolynomial.gradedAlgebra

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: integralLineChart_cocone"; (← IO.getStderr).flush
/-- The canonical singleton cocone leg is the prescribed polynomial projective chart. -/
private theorem integralLineChart_cocone (S : Type u) [CommRing S] (j : ULift.{u} (Fin 2)) :
    Spec.map (CommRingCat.ofHom (integralLineChartEquiv S j).symm.toRingHom) ≫
      ((projectiveLineCocone S).ι.app (.op (integralLineChartIndex j))).left =
        projectiveLinePolynomialChart S j := by
  unfold integralLineChartEquiv projectiveLineCocone
  refine (coordinate_cocone _ _ _ _ _ _).trans ?_
  let U : ULift.{u} (Fin 2) → (projectiveScheme S (ULift.{u} (Fin 2))).Opens := fun k =>
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) S)
      (MvPolynomial.X k)
  let E := (intersectionOpens U ⋙ (projectiveScheme S (ULift.{u} (Fin 2))).restrictFunctor ⋙
    Over.map (projectiveToSpec S (ULift.{u} (Fin 2)))).obj (.op (integralLineChartIndex j))
  exact Subtype.property (p := fun e :
    (algSpec (.of S)).obj (.op (CommAlgCat.of S (Polynomial S))) ≅ E =>
      e.hom.left ≫ ((intersectionOpens U).obj (.op (integralLineChartIndex j))).ι =
        projectiveLinePolynomialChart S j) _

end Part2

section Part3

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: coordinateCocone_naturality"; (← IO.getStderr).flush
private theorem coordinateCocone_naturality {J : Type v} [Category.{w} J]
    {S : Type u} [CommRing S] (D : J ⥤ CommAlgCat.{u} S)
    (c : CategoryTheory.Limits.Cocone (D.op ⋙ algSpec (.of S))) {i j : J} (f : i ⟶ j) :
    Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom) ≫ (c.ι.app (.op i)).left =
      (c.ι.app (.op j)).left :=
  congrArg (fun h => h.left) (c.w f.op)

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: integerLine_chart"; (← IO.getStderr).flush
private theorem integerLine_chart (R : Type u) [CommRing R] [Algebra (ULift.{u} ℤ) R]
    (j : ULift.{u} (Fin 2)) (a : R) (p : Polynomial (ULift.{u} ℤ)) :
    ((integralLineIntegerIso R).hom.app (integralLineChartIndex j)).hom
        (a ⊗ₜ[ℤ] integralLineChartEquiv (ULift.{u} ℤ) j p) =
      integralLineChartEquiv R j (Polynomial.C a * p.map (algebraMap (ULift.{u} ℤ) R)) := by
  change integralLineScalarEquiv (ULift.{u} ℤ) R (integralLineChartIndex j)
    (FrobeniusSplitting.integerScalarEquiv ULift.ringEquiv
      (a ⊗ₜ[ℤ] integralLineChartEquiv (ULift.{u} ℤ) j p)) = _
  rw [FrobeniusSplitting.integerScalarEquiv_tmul, integralLineScalar_chart,
    FrobeniusSplitting.polynomialTensorEquiv_tmul]

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: integerLine_chart_ring"; (← IO.getStderr).flush
private theorem integerLine_chart_ring (R : Type u) [CommRing R] [Algebra (ULift.{u} ℤ) R]
    (j : ULift.{u} (Fin 2)) :
    (CommAlgCat.algEquivOfIso ((integralLineIntegerIso R).app
        (integralLineChartIndex j))).symm.toRingHom.comp
      ((integralLineChartEquiv R j).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap (ULift.{u} ℤ) R))) =
      (Algebra.TensorProduct.includeRight :
        (projectiveLineDiagram (ULift.{u} ℤ)).obj (integralLineChartIndex j) →ₐ[ℤ]
          R ⊗[ℤ] (projectiveLineDiagram (ULift.{u} ℤ)).obj
            (integralLineChartIndex j)).toRingHom.comp
        (integralLineChartEquiv (ULift.{u} ℤ) j).toRingHom := by
  let e := CommAlgCat.algEquivOfIso ((integralLineIntegerIso R).app (integralLineChartIndex j))
  apply RingHom.ext
  intro p
  change e.symm (integralLineChartEquiv R j (p.map (algebraMap (ULift.{u} ℤ) R))) =
    (1 : R) ⊗ₜ[ℤ] integralLineChartEquiv (ULift.{u} ℤ) j p
  have hp := integerLine_chart R j (1 : R) p
  change e ((1 : R) ⊗ₜ[ℤ] integralLineChartEquiv (ULift.{u} ℤ) j p) = _ at hp
  rw [Polynomial.C_1, one_mul] at hp
  rw [← hp]
  exact e.symm_apply_apply _

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: lineChart_cocone_eq"; (← IO.getStderr).flush
private theorem lineChart_cocone_eq (S : Type u) [CommRing S] (j : ULift.{u} (Fin 2)) :
    ((projectiveLineCocone S).ι.app (.op (integralLineChartIndex j))).left =
      Spec.map (CommRingCat.ofHom (integralLineChartEquiv S j).toRingHom) ≫
        projectiveLinePolynomialChart S j := by
  let e : Spec (.of ((projectiveLineDiagram S).obj (integralLineChartIndex j))) ≅
      Spec (.of (Polynomial S)) :=
    Scheme.Spec.mapIso (integralLineChartEquiv S j).toCommRingCatIso.op
  have h : e.inv ≫ ((projectiveLineCocone S).ι.app (.op (integralLineChartIndex j))).left =
      projectiveLinePolynomialChart S j := integralLineChart_cocone S j
  change ((projectiveLineCocone S).ι.app (.op (integralLineChartIndex j))).left =
    e.hom ≫ projectiveLinePolynomialChart S j
  exact (Iso.inv_comp_eq e).mp h

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: integerLine_coeff_chart"; (← IO.getStderr).flush
private theorem integerLine_coeff_chart (R : Type u) [CommRing R]
    [Algebra (ULift.{u} ℤ) R] (j : ULift.{u} (Fin 2)) :
    ((integralLineIntegerCocone R).ι.app (.op (integralLineChartIndex j))).left ≫
        GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap (ULift.{u} ℤ) R) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        (projectiveLineDiagram (ULift.{u} ℤ)).obj (integralLineChartIndex j) →ₐ[ℤ]
          R ⊗[ℤ] (projectiveLineDiagram (ULift.{u} ℤ)).obj
            (integralLineChartIndex j)).toRingHom) ≫
        ((projectiveLineCocone (ULift.{u} ℤ)).ι.app (.op (integralLineChartIndex j))).left := by
  let e := CommAlgCat.algEquivOfIso ((integralLineIntegerIso R).app (integralLineChartIndex j))
  let cR : Spec (.of ((projectiveLineDiagram R).obj (integralLineChartIndex j))) ⟶
      GroupActions.projectiveScheme R (ULift.{u} (Fin 2)) :=
    ((projectiveLineCocone R).ι.app (.op (integralLineChartIndex j))).left
  let cS : Spec (.of ((projectiveLineDiagram (ULift.{u} ℤ)).obj
      (integralLineChartIndex j))) ⟶
      GroupActions.projectiveScheme (ULift.{u} ℤ) (ULift.{u} (Fin 2)) :=
    ((projectiveLineCocone (ULift.{u} ℤ)).ι.app (.op (integralLineChartIndex j))).left
  let inc : (projectiveLineDiagram (ULift.{u} ℤ)).obj (integralLineChartIndex j) →+*
      (FrobeniusSplitting.integerFibreDiagram R (projectiveLineDiagram (ULift.{u} ℤ))).obj
        (integralLineChartIndex j) :=
    Algebra.TensorProduct.includeRight.toRingHom
  have hc : CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap (ULift.{u} ℤ) R)) ≫
      CommRingCat.ofHom (integralLineChartEquiv R j).toRingHom ≫
      CommRingCat.ofHom e.symm.toRingHom =
        CommRingCat.ofHom (integralLineChartEquiv (ULift.{u} ℤ) j).toRingHom ≫
          CommRingCat.ofHom inc := by
    apply CommRingCat.hom_ext
    exact integerLine_chart_ring R j
  let cp := CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap (ULift.{u} ℤ) R))
  let cr := CommRingCat.ofHom (integralLineChartEquiv R j).toRingHom
  let ce := CommRingCat.ofHom e.symm.toRingHom
  let cs := CommRingCat.ofHom (integralLineChartEquiv (ULift.{u} ℤ) j).toRingHom
  let ci := CommRingCat.ofHom inc
  have h1 : Spec.map (cp ≫ cr ≫ ce) = Spec.map ce ≫ Spec.map cr ≫ Spec.map cp :=
    (Spec.map_comp cp (cr ≫ ce)).trans
      ((congrArg (fun f => f ≫ Spec.map cp) (Spec.map_comp cr ce)).trans
        (Category.assoc _ _ _))
  have h2 : Spec.map (cs ≫ ci) = Spec.map ci ≫ Spec.map cs := Spec.map_comp cs ci
  have hs := h1.symm.trans ((congrArg (fun f => Spec.map f) hc).trans h2)
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ cR) ≫ _ =
    Spec.map (CommRingCat.ofHom inc) ≫ cS
  have hR := lineChart_cocone_eq R j
  have hS := lineChart_cocone_eq (ULift.{u} ℤ) j
  change cR = _ at hR
  change cS = _ at hS
  rw [hR, hS]
  change (Spec.map ce ≫ Spec.map cr ≫ projectiveLinePolynomialChart R j) ≫ _ =
    Spec.map ci ≫ Spec.map cs ≫ projectiveLinePolynomialChart (ULift.{u} ℤ) j
  calc
    _ = Spec.map ce ≫ Spec.map cr ≫ (projectiveLinePolynomialChart R j ≫
        GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2))
          (algebraMap (ULift.{u} ℤ) R)) := by simp only [Category.assoc]
    _ = Spec.map ce ≫ Spec.map cr ≫ (Spec.map cp ≫
        projectiveLinePolynomialChart (ULift.{u} ℤ) j) :=
      congrArg (fun f => Spec.map ce ≫ Spec.map cr ≫ f)
        (projectiveLinePolynomial_coeff (ULift.{u} ℤ) R
          (algebraMap (ULift.{u} ℤ) R) j)
    _ = (Spec.map ce ≫ Spec.map cr ≫ Spec.map cp) ≫
        projectiveLinePolynomialChart (ULift.{u} ℤ) j := by simp only [Category.assoc]
    _ = (Spec.map ci ≫ Spec.map cs) ≫ projectiveLinePolynomialChart (ULift.{u} ℤ) j :=
      congrArg (fun f => f ≫ projectiveLinePolynomialChart (ULift.{u} ℤ) j) hs
    _ = _ := Category.assoc _ _ _

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: integerLine_coeff_overlap"; (← IO.getStderr).flush
private theorem integerLine_coeff_overlap (R : Type u) [CommRing R]
    [Algebra (ULift.{u} ℤ) R] :
    ((integralLineIntegerCocone R).ι.app (.op integralLineOverlapIndex)).left ≫
        GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap (ULift.{u} ℤ) R) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        (projectiveLineDiagram (ULift.{u} ℤ)).obj integralLineOverlapIndex →ₐ[ℤ]
          (FrobeniusSplitting.integerFibreDiagram R (projectiveLineDiagram (ULift.{u} ℤ))).obj
            integralLineOverlapIndex).toRingHom) ≫
        ((projectiveLineCocone (ULift.{u} ℤ)).ι.app (.op integralLineOverlapIndex)).left := by
  let G := projectiveLineDiagram (ULift.{u} ℤ)
  let D := FrobeniusSplitting.integerFibreDiagram R G
  let i := integralLineChartIndex (⟨0⟩ : ULift.{u} (Fin 2))
  let j := integralLineOverlapIndex.{u}
  let f : i ⟶ j := integralLineLeftRestriction
  let cRi : Spec (.of (D.obj i)) ⟶ GroupActions.projectiveScheme R (ULift.{u} (Fin 2)) :=
    ((integralLineIntegerCocone R).ι.app (.op i)).left
  let cRj : Spec (.of (D.obj j)) ⟶ GroupActions.projectiveScheme R (ULift.{u} (Fin 2)) :=
    ((integralLineIntegerCocone R).ι.app (.op j)).left
  let cSi : Spec (.of (G.obj i)) ⟶
      GroupActions.projectiveScheme (ULift.{u} ℤ) (ULift.{u} (Fin 2)) :=
    ((projectiveLineCocone (ULift.{u} ℤ)).ι.app (.op i)).left
  let cSj : Spec (.of (G.obj j)) ⟶
      GroupActions.projectiveScheme (ULift.{u} ℤ) (ULift.{u} (Fin 2)) :=
    ((projectiveLineCocone (ULift.{u} ℤ)).ι.app (.op j)).left
  let incI : G.obj i →+* D.obj i := Algebra.TensorProduct.includeRight.toRingHom
  let incJ : G.obj j →+* D.obj j := Algebra.TensorProduct.includeRight.toRingHom
  let df := CommRingCat.ofHom (D.map f).hom.toRingHom
  let gf := CommRingCat.ofHom (G.map f).hom.toRingHom
  let ci := CommRingCat.ofHom incI
  let cj := CommRingCat.ofHom incJ
  have hR : Spec.map df ≫ cRi = cRj :=
    coordinateCocone_naturality D (integralLineIntegerCocone R) f
  have hS : Spec.map gf ≫ cSi = cSj :=
    coordinateCocone_naturality G (projectiveLineCocone (ULift.{u} ℤ)) f
  have hr : ci ≫ df = gf ≫ cj := by
    ext x
    rfl
  have hs : Spec.map df ≫ Spec.map ci = Spec.map cj ≫ Spec.map gf :=
    (Spec.map_comp ci df).symm.trans
      ((congrArg (fun f => Spec.map f) hr).trans (Spec.map_comp gf cj))
  let q := GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap (ULift.{u} ℤ) R)
  have hi : cRi ≫ q = Spec.map ci ≫ cSi := integerLine_coeff_chart R ⟨0⟩
  change cRj ≫ q = Spec.map cj ≫ cSj
  calc
    _ = (Spec.map df ≫ cRi) ≫ q := congrArg (fun f => f ≫ q) hR.symm
    _ = Spec.map df ≫ (cRi ≫ q) := Category.assoc _ _ _
    _ = Spec.map df ≫ (Spec.map ci ≫ cSi) := congrArg (fun f => Spec.map df ≫ f) hi
    _ = (Spec.map df ≫ Spec.map ci) ≫ cSi := (Category.assoc _ _ _).symm
    _ = (Spec.map cj ≫ Spec.map gf) ≫ cSi := congrArg (fun f => f ≫ cSi) hs
    _ = Spec.map cj ≫ (Spec.map gf ≫ cSi) := Category.assoc _ _ _
    _ = _ := congrArg (fun f => Spec.map cj ≫ f) hS

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: lineIndex_cases"; (← IO.getStderr).flush
private theorem lineIndex_cases (s : ProjectiveLineIndex.{u}) :
    s = integralLineChartIndex ⟨0⟩ ∨ s = integralLineChartIndex ⟨1⟩ ∨
      s = integralLineOverlapIndex := by
  classical
  by_cases h0 : (⟨0⟩ : ULift.{u} (Fin 2)) ∈ s.val
  · by_cases h1 : (⟨1⟩ : ULift.{u} (Fin 2)) ∈ s.val
    · right; right
      apply Subtype.ext
      ext ⟨j⟩
      fin_cases j <;> simp [integralLineOverlapIndex, h0, h1]
    · left
      apply Subtype.ext
      ext ⟨j⟩
      fin_cases j <;> simp [integralLineChartIndex, h0, h1]
  · right; left
    have h1 : (⟨1⟩ : ULift.{u} (Fin 2)) ∈ s.val := by
      obtain ⟨⟨j⟩, hj⟩ := s.property
      fin_cases j
      · exact False.elim (h0 hj)
      · exact hj
    apply Subtype.ext
    ext ⟨j⟩
    fin_cases j <;> simp [integralLineChartIndex, h0, h1]

run_cmd do if Lean.profiler.get (← Lean.MonadOptions.getOptions) then do
  IO.eprintln "ModelMaps: integralLineInteger_model_map"; (← IO.getStderr).flush
/-- The coefficient morphism is cartesian and commutes with every integral coordinate leg. -/
theorem integralLineInteger_model_map (R : Type u) [CommRing R]
    [Algebra (ULift.{u} ℤ) R] :
    IsPullback (GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2))
        (algebraMap (ULift.{u} ℤ) R))
      (integralLineIntegerCocone R).pt.hom (projectiveLineCocone (ULift.{u} ℤ)).pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R))) ∧
      ∀ s : ProjectiveLineIndex.{u},
        ((integralLineIntegerCocone R).ι.app (.op s)).left ≫
            GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2))
              (algebraMap (ULift.{u} ℤ) R) =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            (projectiveLineDiagram (ULift.{u} ℤ)).obj s →ₐ[ℤ]
              (FrobeniusSplitting.integerFibreDiagram R
                (projectiveLineDiagram (ULift.{u} ℤ))).obj s).toRingHom) ≫
            ((projectiveLineCocone (ULift.{u} ℤ)).ι.app (.op s)).left := by
  refine ⟨integralLineInteger_cartesian R, fun s ↦ ?_⟩
  rcases lineIndex_cases s with rfl | rfl | rfl
  · exact integerLine_coeff_chart R ⟨0⟩
  · exact integerLine_coeff_chart R ⟨1⟩
  · exact integerLine_coeff_overlap R

end Part3

end SchubertGeometry
