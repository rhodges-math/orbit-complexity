import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoDescent
import Mathlib.Data.Fintype.Basic

/-!
# Joint finite retention on prescribed scalar models

-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u v

private theorem finite_stage_bound {I J : Type*} [Fintype I] [Preorder J]
    [IsDirectedOrder J] (i : I → J) (start : J) :
    ∃ j : J, start ≤ j ∧ ∀ r, i r ≤ j := by
  classical
  have h : ∀ s : Finset I, ∃ j : J, start ≤ j ∧ ∀ r ∈ s, i r ≤ j := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨start, le_rfl, by intro r hr; simp at hr⟩
    | @insert r s _ ih =>
      obtain ⟨j, hstart, hj⟩ := ih
      obtain ⟨k, hjk, hrk⟩ := exists_ge_ge j (i r)
      refine ⟨k, hstart.trans hjk, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hrk
      · exact (hj t ht).trans hjk
  obtain ⟨j, hj, hall⟩ := h Finset.univ
  exact ⟨j, hj, fun r => hall r (Finset.mem_univ r)⟩

variable {K : Type u} [CommRing K] (S : Subalgebra ℤ K)

private theorem retained_transition_comp
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j k : CoefficientStage S} (hij : i ≤ j) (hjk : j ≤ k) :
    stageScalarTransition S a hjk ≫ stageScalarTransition S a hij =
      stageScalarTransition S a (hij.trans hjk) := by
  let D := modelScalarStages S a
  have h : (homOfLE hjk).op ≫ (homOfLE hij).op =
      (homOfLE (hij.trans hjk)).op := Subsingleton.elim _ _
  exact (D.map_comp ((homOfLE hjk).op) ((homOfLE hij).op)).symm.trans
    (congrArg (fun q => D.map q) h)

private theorem retained_equation_later
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j k : CoefficientStage S} (hij : i ≤ j) (hjk : j ≤ k)
    (f g : (stageScalarModel S a i).left ⟶ Y)
    (h : stageScalarTransition S a hij ≫ f = stageScalarTransition S a hij ≫ g) :
    stageScalarTransition S a (hij.trans hjk) ≫ f =
      stageScalarTransition S a (hij.trans hjk) ≫ g := by
  calc
    stageScalarTransition S a (hij.trans hjk) ≫ f =
        (stageScalarTransition S a hjk ≫ stageScalarTransition S a hij) ≫ f :=
      congrArg (fun q => q ≫ f) (retained_transition_comp S a hij hjk).symm
    _ = stageScalarTransition S a hjk ≫ (stageScalarTransition S a hij ≫ f) :=
      Category.assoc _ _ _
    _ = stageScalarTransition S a hjk ≫ (stageScalarTransition S a hij ≫ g) :=
      congrArg (fun q => stageScalarTransition S a hjk ≫ q) h
    _ = (stageScalarTransition S a hjk ≫ stageScalarTransition S a hij) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = stageScalarTransition S a (hij.trans hjk) ≫ g :=
      congrArg (fun q => q ≫ g) (retained_transition_comp S a hij hjk)

/-- Cartesian extension of the prescribed stage maps preserves their composition. -/
theorem retainedMap_comp
    {X Y Z : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S)) (c : Z ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : stageScalarModel S b i ⟶ stageScalarModel S c i) :
    extendModelMorphism S a b hij f ≫ extendModelMorphism S b c hij g =
      extendModelMorphism S a c hij (f ≫ g) := by
  apply Over.OverMorphism.ext
  apply (stageScalarCartesian S c hij).hom_ext
  · change ((extendModelMorphism S a b hij f).left ≫
        (extendModelMorphism S b c hij g).left) ≫ stageScalarTransition S c hij =
      (extendModelMorphism S a c hij (f ≫ g)).left ≫ stageScalarTransition S c hij
    calc
      ((extendModelMorphism S a b hij f).left ≫
          (extendModelMorphism S b c hij g).left) ≫ stageScalarTransition S c hij =
          (extendModelMorphism S a b hij f).left ≫
            ((extendModelMorphism S b c hij g).left ≫ stageScalarTransition S c hij) :=
        Category.assoc _ _ _
      _ = (extendModelMorphism S a b hij f).left ≫
          (stageScalarTransition S b hij ≫ g.left) :=
        congrArg (fun q => (extendModelMorphism S a b hij f).left ≫ q)
          (extendModelMorphism_transition S b c hij g)
      _ = ((extendModelMorphism S a b hij f).left ≫ stageScalarTransition S b hij) ≫
          g.left := (Category.assoc _ _ _).symm
      _ = (stageScalarTransition S a hij ≫ f.left) ≫ g.left :=
        congrArg (fun q => q ≫ g.left) (extendModelMorphism_transition S a b hij f)
      _ = stageScalarTransition S a hij ≫ (f ≫ g).left := Category.assoc _ _ _
      _ = (extendModelMorphism S a c hij (f ≫ g)).left ≫ stageScalarTransition S c hij :=
        (extendModelMorphism_transition S a c hij (f ≫ g)).symm
  · exact (extendModelMorphism S a b hij f ≫ extendModelMorphism S b c hij g).w.trans
      (extendModelMorphism S a c hij (f ≫ g)).w.symm

/-- Cartesian extension of the prescribed stage maps preserves the identity. -/
theorem retainedMap_id
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) :
    extendModelMorphism S a a hij (𝟙 (stageScalarModel S a i)) =
      𝟙 (stageScalarModel S a j) := by
  apply Over.OverMorphism.ext
  apply (stageScalarCartesian S a hij).hom_ext
  · change (extendModelMorphism S a a hij (𝟙 _)).left ≫ stageScalarTransition S a hij =
      𝟙 _ ≫ stageScalarTransition S a hij
    exact (extendModelMorphism_transition S a a hij (𝟙 _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · exact (extendModelMorphism S a a hij (𝟙 _)).w.trans (Category.id_comp _).symm

/-- Extend the same stage isomorphism, with both inverse equations proved by the
functor laws of the original Cartesian extension. -/
def retainedIsoExtend
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (E : stageScalarModel S a i ≅ stageScalarModel S b i) :
    stageScalarModel S a j ≅ stageScalarModel S b j where
  hom := extendModelMorphism S a b hij E.hom
  inv := extendModelMorphism S b a hij E.inv
  hom_inv_id := by
    rw [retainedMap_comp, E.hom_inv_id, retainedMap_id]
  inv_hom_id := by
    rw [retainedMap_comp, E.inv_hom_id, retainedMap_id]

/-- Finitely many specified generic isomorphisms of fixed models descend
jointly above any prescribed coefficient stage. Both original directions remain. -/
theorem exists_retained_isos
    {I : Type v} [Fintype I] (hS : S.FG)
    (X Y : I → Scheme.{u})
    [∀ r, CompactSpace (X r)] [∀ r, QuasiSeparatedSpace (X r)]
    [∀ r, CompactSpace (Y r)] [∀ r, QuasiSeparatedSpace (Y r)]
    (a : ∀ r, X r ⟶ Spec (.of S)) (b : ∀ r, Y r ⟶ Spec (.of S))
    [∀ r, LocallyOfFinitePresentation (a r)] [∀ r, LocallyOfFinitePresentation (b r)]
    (E : ∀ r, genericScalarModel S (a r) ≅ genericScalarModel S (b r))
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S) (_ : start ≤ j)
      (E₀ : ∀ r, stageScalarModel S (a r) j ≅ stageScalarModel S (b r) j),
      (∀ r, (modelScalarCone S (a r)).π.app (op j) ≫ (E₀ r).hom.left =
        (E r).hom.left ≫ (modelScalarCone S (b r)).π.app (op j)) ∧
      (∀ r, (modelScalarCone S (b r)).π.app (op j) ≫ (E₀ r).inv.left =
        (E r).inv.left ≫ (modelScalarCone S (a r)).π.app (op j)) := by
  classical
  choose i Ei hhom hinv using fun r => exists_model_iso S hS (a r) (b r) (E r)
  obtain ⟨j, hstart, hij⟩ := finite_stage_bound i start
  let E₀ r := retainedIsoExtend S (a r) (b r) (hij r) (Ei r)
  refine ⟨j, hstart, E₀, ?_, ?_⟩
  · intro r
    exact extendModelMorphism_baseChange S (a r) (b r) (hij r) (Ei r).hom
      (E r).hom (hhom r)
  · intro r
    exact extendModelMorphism_baseChange S (b r) (a r) (hij r) (Ei r).inv
      (E r).inv (hinv r)

/-- Finitely many generic equalities are retained together by restriction of
the same maps from the same stage models to their original targets. -/
theorem exists_retained_equations
    {I : Type v} [Fintype I] (hS : S.FG)
    (X Y : I → Scheme.{u})
    [∀ r, CompactSpace (X r)] [∀ r, QuasiSeparatedSpace (X r)]
    (a : ∀ r, X r ⟶ Spec (.of S)) (b : ∀ r, Y r ⟶ Spec (.of S))
    [∀ r, LocallyOfFiniteType (b r)]
    (i : CoefficientStage S)
    (f g : ∀ r, (stageScalarModel S (a r) i).left ⟶ Y r)
    (hf : ∀ r, f r ≫ b r = (modelScalarBase S (a r)).app (op i))
    (hg : ∀ r, g r ≫ b r = (modelScalarBase S (a r)).app (op i))
    (heq : ∀ r, (modelScalarCone S (a r)).π.app (op i) ≫ f r =
      (modelScalarCone S (a r)).π.app (op i) ≫ g r) :
    ∃ (j : CoefficientStage S) (hij : i ≤ j), ∀ r,
      stageScalarTransition S (a r) hij ≫ f r =
        stageScalarTransition S (a r) hij ≫ g r := by
  classical
  choose j hij hj using fun r =>
    exists_scalar_equality S hS (a r) (b r) i (f r) (g r) (hf r) (hg r) (heq r)
  obtain ⟨k, hik, hjk⟩ := finite_stage_bound j i
  refine ⟨k, hik, ?_⟩
  intro r
  have hr : stageScalarTransition S (a r) (hij r) ≫ f r =
      stageScalarTransition S (a r) (hij r) ≫ g r := hj r
  exact retained_equation_later S (a r) (hij r) (hjk r) (f r) (g r) hr

end FrobeniusSplitting
