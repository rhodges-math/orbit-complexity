import OrbitComplexity.FrobeniusSplitting.Normality.Limits.CoefficientLimit
import OrbitComplexity.SchubertGeometry.Parabolics.CurveFibre

/-! # Retaining the Weyl point of a simple partial-flag model -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ReductiveGroups
open FrobeniusSplitting

namespace SchubertGeometry

universe u

/-- The chosen partial Weyl flag descends to an point of the
specified model over one finite coefficient extension, with its original square. -/
theorem exists_weyl_partial_point
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (w : G.weylGroup) (i : G.rootBase.support)
    {Q : Scheme.{u}} (aQ : Q ⟶ Spec (.of S)) [LocallyOfFinitePresentation aQ]
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q)
    (hqQ : qQ ≫ aQ = (partialFlagVariety G {i}).toSpec ≫
      Spec.map (CommRingCat.ofHom (algebraMap S K))) :
    ∃ (r : CoefficientStage S) (b : Spec (.of r.val) ⟶ Q),
      b ≫ aQ = Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion r.property.2).toRingHom) ∧
      ((weylFlagPoint G w).val ≫ (partialFlagMorphism G {i}).left) ≫ qQ =
        Spec.map (CommRingCat.ofHom (algebraMap r.val K)) ≫ b := by
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  let t : coefficientSchemes S ⟶ (Functor.const _).obj (Spec (.of S)) :=
    { app := fun j => Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion j.unop.property.2).toRingHom)
      naturality := fun j k f => by
        change (coefficientSchemes S).map f ≫ _ = _ ≫ 𝟙 _
        exact (Spec.map_comp
          (CommRingCat.ofHom (Subalgebra.inclusion k.unop.property.2).toRingHom)
          ((coefficientRings S).map f.unop)).symm.trans (Category.comp_id _).symm }
  let z := (weylFlagPoint G w).val ≫ (partialFlagMorphism G {i}).left
  have hz : z ≫ (partialFlagVariety G {i}).toSpec = 𝟙 _ := by
    have hπ : (partialFlagMorphism G {i}).left ≫
        (partialFlagVariety G {i}).toSpec = (flagVariety G).toSpec :=
      (partialFlagMorphism G {i}).w
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => (weylFlagPoint G w).val ≫ q) hπ).trans
        (weylFlagPoint G w).property)
  have hbase : (coefficientSpecCone S).π ≫ t =
      (Functor.const _).map ((z ≫ qQ) ≫ aQ) := by
    ext j
    change Spec.map (CommRingCat.ofHom (algebraMap j.unop.val K)) ≫
      Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion j.unop.property.2).toRingHom) = (z ≫ qQ) ≫ aQ
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap S K)) :=
        (Spec.map_comp
          (CommRingCat.ofHom (Subalgebra.inclusion j.unop.property.2).toRingHom)
          (CommRingCat.ofHom (algebraMap j.unop.val K))).symm
      _ = (z ≫ qQ) ≫ aQ := by
        rw [Category.assoc, hqQ, ← Category.assoc, hz, Category.id_comp]
  let : ∀ {j k : (CoefficientStage S)ᵒᵖ} (f : j ⟶ k),
      IsAffineHom ((coefficientSchemes S).map f) := fun f => by
    change IsAffineHom (Spec.map _)
    infer_instance
  let : ∀ j, CompactSpace ((coefficientSchemes S).obj j) := fun j => by
    change CompactSpace (Spec _)
    infer_instance
  let : ∀ j, QuasiSeparatedSpace ((coefficientSchemes S).obj j) := fun j => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  obtain ⟨r, b, hnative, hstructure⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (coefficientSchemes S) t aQ (coefficientSpecCone S)
      (coefficientSpecLimit S hS) (z ≫ qQ) hbase
  exact ⟨r.unop, b, hstructure, hnative.symm⟩


end SchubertGeometry
