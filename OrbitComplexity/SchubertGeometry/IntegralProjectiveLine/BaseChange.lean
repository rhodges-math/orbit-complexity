import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Coordinates
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.IntegerTensors
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected

/-! # Scalar extension of the integral projective-line coordinate diagram -/

noncomputable section

universe u v w

namespace SchubertGeometry

section Part1

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

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

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- Each canonical projective-line coordinate ring commutes with scalar extension. -/
noncomputable def integralLineScalarEquiv (s : ProjectiveLineIndex.{u}) :
    R ⊗[S] (projectiveLineDiagram S).obj s ≃ₐ[R] (projectiveLineDiagram R).obj s := by
  classical
  by_cases h0 : s = integralLineChartIndex ⟨0⟩
  · subst s
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
      (integralLineChartEquiv S ⟨0⟩).symm).trans
        ((FrobeniusSplitting.polynomialTensorEquiv S R).trans (integralLineChartEquiv R ⟨0⟩))
  by_cases h1 : s = integralLineChartIndex ⟨1⟩
  · subst s
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
      (integralLineChartEquiv S ⟨1⟩).symm).trans
        ((FrobeniusSplitting.polynomialTensorEquiv S R).trans (integralLineChartEquiv R ⟨1⟩))
  have h2 : s = integralLineOverlapIndex := (lineIndex_cases s).resolve_left h0 |>.resolve_left h1
  subst s
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
    (integralLineOverlapEquiv S).symm).trans
      ((AddMonoidAlgebra.scalarTensorEquiv S R).trans (integralLineOverlapEquiv R))

end Part1

section Part2

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The singleton scalar comparison preserves the specified polynomial coordinates. -/
theorem integralLineScalar_chart (j : ULift.{u} (Fin 2)) (a : R) (p : Polynomial S) :
    integralLineScalarEquiv S R (integralLineChartIndex j)
        (a ⊗ₜ[S] integralLineChartEquiv S j p) =
      integralLineChartEquiv R j (FrobeniusSplitting.polynomialTensorEquiv S R (a ⊗ₜ[S] p)) := by
  have hj : j = ⟨0⟩ ∨ j = ⟨1⟩ := by
    rcases j with ⟨j⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hj with rfl | rfl
  · simpa only [integralLineScalarEquiv, dite_true] using
      (FrobeniusSplitting.tensorCoordinate_apply (integralLineChartEquiv S ⟨0⟩)
        (FrobeniusSplitting.polynomialTensorEquiv S R) (integralLineChartEquiv R ⟨0⟩) a p)
  · have h10 : integralLineChartIndex.{u} ⟨1⟩ ≠ integralLineChartIndex ⟨0⟩ := by decide
    simpa only [integralLineScalarEquiv, dite_eq_right h10, dite_true] using
      (FrobeniusSplitting.tensorCoordinate_apply (integralLineChartEquiv S ⟨1⟩)
        (FrobeniusSplitting.polynomialTensorEquiv S R) (integralLineChartEquiv R ⟨1⟩) a p)

/-- The overlap scalar comparison preserves the specified Laurent coordinate. -/
private theorem integralLineScalar_overlap (a : R) (p : LaurentPolynomial S) :
    integralLineScalarEquiv S R integralLineOverlapIndex
        (a ⊗ₜ[S] integralLineOverlapEquiv S p) =
      integralLineOverlapEquiv R ((AddMonoidAlgebra.scalarTensorEquiv S R) (a ⊗ₜ[S] p)) := by
  have h0 : integralLineOverlapIndex.{u} ≠ integralLineChartIndex ⟨0⟩ := by decide
  have h1 : integralLineOverlapIndex.{u} ≠ integralLineChartIndex ⟨1⟩ := by decide
  simpa only [integralLineScalarEquiv, dite_eq_right h0, dite_eq_right h1] using
    (FrobeniusSplitting.tensorCoordinate_apply (integralLineOverlapEquiv S)
      (AddMonoidAlgebra.scalarTensorEquiv S R) (integralLineOverlapEquiv R) a p)

/-- The first canonical restriction commutes with the coordinate scalar comparison. -/
private theorem integralLineScalar_left (a : R)
    (x : (projectiveLineDiagram S).obj (integralLineChartIndex ⟨0⟩)) :
    integralLineScalarEquiv S R integralLineOverlapIndex
        (a ⊗ₜ[S] ((projectiveLineDiagram S).map integralLineLeftRestriction).hom x) =
      ((projectiveLineDiagram R).map integralLineLeftRestriction).hom
        (integralLineScalarEquiv S R (integralLineChartIndex ⟨0⟩) (a ⊗ₜ[S] x)) := by
  obtain ⟨p, rfl⟩ := (integralLineChartEquiv S ⟨0⟩).surjective x
  rw [integralLineRestriction_left, integralLineScalar_overlap, integralLineScalar_chart,
    integralLineRestriction_left, FrobeniusSplitting.polynomialTensor_toLaurent]

/-- The reciprocal restriction commutes with the coordinate scalar comparison. -/
private theorem integralLineScalar_right (a : R)
    (x : (projectiveLineDiagram S).obj (integralLineChartIndex ⟨1⟩)) :
    integralLineScalarEquiv S R integralLineOverlapIndex
        (a ⊗ₜ[S] ((projectiveLineDiagram S).map integralLineRightRestriction).hom x) =
      ((projectiveLineDiagram R).map integralLineRightRestriction).hom
        (integralLineScalarEquiv S R (integralLineChartIndex ⟨1⟩) (a ⊗ₜ[S] x)) := by
  obtain ⟨p, rfl⟩ := (integralLineChartEquiv S ⟨1⟩).surjective x
  rw [integralLineRestriction_right, integralLineScalar_overlap, integralLineScalar_chart,
    integralLineRestriction_right, FrobeniusSplitting.laurentTensor_invert,
    FrobeniusSplitting.polynomialTensor_toLaurent]

end Part2

section Part3

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

private theorem noHom_of_mem (s t : ProjectiveLineIndex.{u})
    (r : ULift.{u} (Fin 2)) (hr : r ∈ s.val) (hn : r ∉ t.val) (f : s ⟶ t) : False :=
  hn ((show s.val ⊆ t.val from leOfHom f) hr)

/-- Naturality on the two chart restrictions identifies the projective-line diagrams. -/
private noncomputable def integralLine_naturality
    (R : Type u) [rComm : CommRing R]
    (F G : ProjectiveLineIndex.{u} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, F.obj s ≃ₐ[R] G.obj s)
    (hleft : (e integralLineOverlapIndex).toAlgHom.comp
        (F.map integralLineLeftRestriction).hom =
      (G.map integralLineLeftRestriction).hom.comp
        (e (integralLineChartIndex ⟨0⟩)).toAlgHom)
    (hright : (e integralLineOverlapIndex).toAlgHom.comp
        (F.map integralLineRightRestriction).hom =
      (G.map integralLineRightRestriction).hom.comp
        (e (integralLineChartIndex ⟨1⟩)).toAlgHom) : F ≅ G := by
  refine @NatIso.ofComponents.{u,u,u,u+1} ProjectiveLineIndex
    (inferInstanceAs (Category ProjectiveLineIndex)) (CommAlgCat.{u} R)
    (@CommAlgCat.instCategory.{u,u} R rComm) F G
    (fun s => CommAlgCat.isoMk (e s)) ?_
  intro s t f
  apply CommAlgCat.hom_ext
  change (e t).toAlgHom.comp (F.map f).hom = (G.map f).hom.comp (e s).toAlgHom
  classical
  rcases lineIndex_cases s with rfl | rfl | rfl <;>
    rcases lineIndex_cases t with rfl | rfl | rfl
  · have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp
  · exact (noHom_of_mem _ _ ⟨0⟩ (by simp [integralLineChartIndex])
      (by simp [integralLineChartIndex]) f).elim
  · have hf : f = integralLineLeftRestriction := Subsingleton.elim _ _
    simpa only [hf] using hleft
  · exact (noHom_of_mem _ _ ⟨1⟩ (by simp [integralLineChartIndex])
      (by simp [integralLineChartIndex]) f).elim
  · have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp
  · have hf : f = integralLineRightRestriction := Subsingleton.elim _ _
    simpa only [hf] using hright
  · exact (noHom_of_mem _ _ ⟨1⟩ (by simp [integralLineOverlapIndex])
      (by simp [integralLineChartIndex]) f).elim
  · exact (noHom_of_mem _ _ ⟨0⟩ (by simp [integralLineOverlapIndex])
      (by simp [integralLineChartIndex]) f).elim
  · have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The canonical projective-line diagrams commute naturally with coefficient extension. -/
private noncomputable def integralLineScalarIso :
    FrobeniusSplitting.fixedFibreDiagram (R := R) (M := R) (projectiveLineDiagram S) ≅
      projectiveLineDiagram R := by
  let F := FrobeniusSplitting.fixedFibreDiagram (R := R) (M := R) (projectiveLineDiagram S)
  let G := projectiveLineDiagram R
  have hleft : (integralLineScalarEquiv S R integralLineOverlapIndex).toAlgHom.comp
        (F.map integralLineLeftRestriction).hom =
      (G.map integralLineLeftRestriction).hom.comp
        (integralLineScalarEquiv S R (integralLineChartIndex ⟨0⟩)).toAlgHom := by
    exact FrobeniusSplitting.tensor_map_naturality
      (integralLineScalarEquiv S R (integralLineChartIndex ⟨0⟩))
      (integralLineScalarEquiv S R integralLineOverlapIndex)
      ((projectiveLineDiagram S).map integralLineLeftRestriction).hom
      ((projectiveLineDiagram R).map integralLineLeftRestriction).hom
      (integralLineScalar_left S R)
  have hright : (integralLineScalarEquiv S R integralLineOverlapIndex).toAlgHom.comp
        (F.map integralLineRightRestriction).hom =
      (G.map integralLineRightRestriction).hom.comp
        (integralLineScalarEquiv S R (integralLineChartIndex ⟨1⟩)).toAlgHom := by
    exact FrobeniusSplitting.tensor_map_naturality
      (integralLineScalarEquiv S R (integralLineChartIndex ⟨1⟩))
      (integralLineScalarEquiv S R integralLineOverlapIndex)
      ((projectiveLineDiagram S).map integralLineRightRestriction).hom
      ((projectiveLineDiagram R).map integralLineRightRestriction).hom
      (integralLineScalar_right S R)
  exact @integralLine_naturality.{u} R (inferInstanceAs (CommRing R)) F G
    (integralLineScalarEquiv S R) hleft hright

end Part3

section Part4

open CategoryTheory

/-- The integral three-node diagram gives the projective line after base change. -/
noncomputable def integralLineIntegerIso (R : Type u) [CommRing R]
    [Algebra (ULift.{u} ℤ) R] :
    FrobeniusSplitting.integerFibreDiagram R (projectiveLineDiagram (ULift.{u} ℤ)) ≅
      projectiveLineDiagram R :=
  FrobeniusSplitting.integerCoordinateScalarIso R ULift.ringEquiv
    (projectiveLineDiagram (ULift.{u} ℤ)) ≪≫
    integralLineScalarIso (ULift.{u} ℤ) R

end Part4

section Part5

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (R : Type u) [CommRing R] [Algebra (ULift.{u} ℤ) R]

private noncomputable def integerLineSpecIso :
    (FrobeniusSplitting.integerFibreDiagram R
      (projectiveLineDiagram (ULift.{u} ℤ))).op ⋙ algSpec (.of R) ≅
        (projectiveLineDiagram R).op ⋙ algSpec (.of R) :=
  Functor.isoWhiskerRight (NatIso.op (integralLineIntegerIso R).symm) (algSpec (.of R))

/-- Tensoring the integral coordinate rings gives a cocone with projective-line vertex. -/
noncomputable def integralLineIntegerCocone :
    Cocone ((FrobeniusSplitting.integerFibreDiagram R
      (projectiveLineDiagram (ULift.{u} ℤ))).op ⋙ algSpec (.of R)) :=
  (Cocone.precompose (integerLineSpecIso R).hom).obj (projectiveLineCocone R)

/-- The specified projective-line cocone is the colimit of the integer tensor diagram. -/
noncomputable def integralLineIntegerColimit : IsColimit (integralLineIntegerCocone R) :=
  (IsColimit.precomposeHomEquiv (integerLineSpecIso R) _).symm
    (projectiveLineCoconeIsColimit R)

/-- The integral nodes are flat and finitely presented, and the model vertex has P¹ geometry. -/
theorem integralLineInteger_properties :
    (∀ s : ProjectiveLineIndex.{u},
      Algebra.FinitePresentation ℤ ((projectiveLineDiagram (ULift.{u} ℤ)).obj s) ∧
        Module.Flat ℤ ((projectiveLineDiagram (ULift.{u} ℤ)).obj s)) ∧
      IsProper (integralLineIntegerCocone R).pt.hom ∧
      Smooth (integralLineIntegerCocone R).pt.hom ∧
      GeometricallyConnected (integralLineIntegerCocone R).pt.hom := by
  refine ⟨fun s ↦ ⟨inferInstance, inferInstance⟩, ?_⟩
  change IsProper (GroupActions.projectiveToSpec R (ULift.{u} (Fin 2))) ∧
    Smooth (GroupActions.projectiveToSpec R (ULift.{u} (Fin 2))) ∧
    GeometricallyConnected (GroupActions.projectiveToSpec R (ULift.{u} (Fin 2)))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The coefficient morphism gives the cartesian comparison with the integral projective line. -/
theorem integralLineInteger_cartesian :
    IsPullback (GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2))
        (algebraMap (ULift.{u} ℤ) R))
      (integralLineIntegerCocone R).pt.hom (projectiveLineCocone (ULift.{u} ℤ)).pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R))) := by
  let e := GroupActions.projectiveBaseChange (ULift.{u} (Fin 2))
    (algebraMap (ULift.{u} ℤ) R)
  have hf := GroupActions.projectiveBaseChange_fst (ULift.{u} (Fin 2))
    (algebraMap (ULift.{u} ℤ) R)
  have hg := GroupActions.projectiveBaseChange_snd (ULift.{u} (Fin 2))
    (algebraMap (ULift.{u} ℤ) R)
  have hcart : IsPullback (GroupActions.projectiveToSpec R (ULift.{u} (Fin 2)))
      (GroupActions.projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap (ULift.{u} ℤ) R))
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R)))
      (GroupActions.projectiveToSpec (ULift.{u} ℤ) (ULift.{u} (Fin 2))) := by
    apply IsPullback.of_iso_pullback ⟨?_⟩ e hf hg
    rw [← hf, ← hg, Category.assoc, Category.assoc, pullback.condition]
  exact hcart.flip

end Part5

end SchubertGeometry
