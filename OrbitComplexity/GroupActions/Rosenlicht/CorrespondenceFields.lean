import OrbitComplexity.GroupActions.Rosenlicht.ClosedCorrespondenceFields
import OrbitComplexity.GroupActions.Rosenlicht.ProductOpenCharts

/-!
# Function fields of closed correspondences

A nonempty affine chart in each factor restricts a closed correspondence to
an affine correspondence. Dominant projections ensure that the restriction
is nonempty. The induced open immersions transfer the generation statement
back to the original function field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable (K : Type u) [Field K] (X Y : Scheme.{u})
variable [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [IsIntegral X] [IsIntegral Y]

private lemma chartField_adjoin {Z : Scheme.{u}} [IsIntegral Z]
    [Algebra K Z.functionField] (i : Z ⟶ pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
    [IsClosedImmersion i]
    [IsDominant (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))]
    [IsDominant (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))]
    (U : X.Opens) (V : Y.Opens) (hUa : IsAffineOpen U) (hVa : IsAffineOpen V)
    (hU : (U : Set X).Nonempty) (hV : (V : Set Y).Nonempty) :
    IntermediateField.adjoin K
      (Set.range (functionFieldMap
        (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))) ∪
       Set.range (functionFieldMap
        (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))))) = ⊤ := by
  let f := X ↘ Spec (.of K)
  let g := Y ↘ Spec (.of K)
  let j := productOpenMap f g U V
  let W := pullback i j
  let w : W ⟶ Z := pullback.fst i j
  let k : W ⟶ pullback (U.ι ≫ f) (V.ι ≫ g) := pullback.snd i j
  have hk : IsClosedImmersion k := by
    dsimp only [k]
    infer_instance
  have : Nonempty W := productChart_pullback_nonempty f g U V i hU hV
  have : IsIntegral W := isIntegral_of_isOpenImmersion w
  have : IsDominant w := ⟨w.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty w)⟩
  have : Nonempty U := Set.nonempty_coe_sort.mpr hU
  have : Nonempty V := Set.nonempty_coe_sort.mpr hV
  have : IsAffine U.toScheme := hUa
  have : IsAffine V.toScheme := hVa
  let _ : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ f⟩
  let _ : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ g⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hU)
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense hV)
  let p := k ≫ pullback.fst (U.ι ≫ f) (V.ι ≫ g)
  let q := k ≫ pullback.snd (U.ι ≫ f) (V.ι ≫ g)
  have hc : w ≫ i = k ≫ j := pullback.condition (f := i) (g := j)
  have hp : p ≫ U.ι = w ≫ (i ≫ pullback.fst f g) := by
    dsimp only [p]
    rw [Category.assoc, ← productOpenMap_fst]
    change k ≫ (j ≫ pullback.fst f g) = _
    rw [← Category.assoc, ← hc, Category.assoc]
  have hq : q ≫ V.ι = w ≫ (i ≫ pullback.snd f g) := by
    dsimp only [q]
    rw [Category.assoc, ← productOpenMap_snd]
    change k ≫ (j ≫ pullback.snd f g) = _
    rw [← Category.assoc, ← hc, Category.assoc]
  have : IsDominant (p ≫ U.ι) := by rw [hp]; infer_instance
  have : IsDominant (q ≫ V.ι) := by rw [hq]; infer_instance
  have : IsDominant p := IsDominant.of_comp_of_isOpenImmersion p U.ι
  have : IsDominant q := IsDominant.of_comp_of_isOpenImmersion q V.ι
  let e₀ := openFunctionFieldEquiv w
  let _ : Algebra K W.functionField :=
    (e₀.toRingHom.comp (algebraMap K Z.functionField)).toAlgebra
  let e : Z.functionField ≃ₐ[K] W.functionField :=
    { e₀ with commutes' := fun _ ↦ rfl }
  let E := IntermediateField.adjoin K
    (Set.range (functionFieldMap (i ≫ pullback.fst f g)) ∪
      Set.range (functionFieldMap (i ≫ pullback.snd f g)))
  have hl : Set.range (functionFieldMap p) ⊆ E.map e.toAlgHom := by
    rintro z ⟨u, rfl⟩
    obtain ⟨a, ha⟩ := (openFunctionFieldEquiv U.ι).surjective u
    have he : functionFieldMap p u = e (functionFieldMap (i ≫ pullback.fst f g) a) := by
      change functionFieldMap p u = functionFieldMap w
        (functionFieldMap (i ≫ pullback.fst f g) a)
      calc
        _ = functionFieldMap (p ≫ U.ι) a := by
          rw [functionFieldMap_comp p U.ι, RingHom.comp_apply]
          change functionFieldMap p u = functionFieldMap p (openFunctionFieldEquiv U.ι a)
          rw [ha]
        _ = functionFieldMap (w ≫ (i ≫ pullback.fst f g)) a := by rw [functionFieldMap_congr _ _ hp]
        _ = _ := by rw [functionFieldMap_comp w (i ≫ pullback.fst f g), RingHom.comp_apply]
    exact (IntermediateField.mem_map E).mpr
      ⟨functionFieldMap (i ≫ pullback.fst f g) a,
        IntermediateField.subset_adjoin K _ (Or.inl ⟨a, rfl⟩), he.symm⟩
  have hr : Set.range (functionFieldMap q) ⊆ E.map e.toAlgHom := by
    rintro z ⟨u, rfl⟩
    obtain ⟨b, hb⟩ := (openFunctionFieldEquiv V.ι).surjective u
    have he : functionFieldMap q u = e (functionFieldMap (i ≫ pullback.snd f g) b) := by
      change functionFieldMap q u = functionFieldMap w
        (functionFieldMap (i ≫ pullback.snd f g) b)
      calc
        _ = functionFieldMap (q ≫ V.ι) b := by
          rw [functionFieldMap_comp q V.ι, RingHom.comp_apply]
          change functionFieldMap q u = functionFieldMap q (openFunctionFieldEquiv V.ι b)
          rw [hb]
        _ = functionFieldMap (w ≫ (i ≫ pullback.snd f g)) b := by rw [functionFieldMap_congr _ _ hq]
        _ = _ := by rw [functionFieldMap_comp w (i ≫ pullback.snd f g), RingHom.comp_apply]
    exact (IntermediateField.mem_map E).mpr
      ⟨functionFieldMap (i ≫ pullback.snd f g) b,
        IntermediateField.subset_adjoin K _ (Or.inr ⟨b, rfl⟩), he.symm⟩
  have hg := @closedProductField_adjoin K inferInstance U.toScheme V.toScheme
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    W inferInstance inferInstance k hk ‹IsDominant p› ‹IsDominant q›
  have ht : (⊤ : IntermediateField K W.functionField) ≤ E.map e.toAlgHom := by
    rw [← hg]
    exact IntermediateField.adjoin_le_iff.mpr (Set.union_subset hl hr)
  apply top_le_iff.mp
  intro z _
  obtain ⟨a, ha, he⟩ := (IntermediateField.mem_map E).mp (ht (show e z ∈ ⊤ from trivial))
  exact e.injective he ▸ ha

/-- Dominant projections from an integral closed correspondence generate its
function field over the common base field. -/
theorem closedProductField_adjoin_general {Z : Scheme.{u}} [IsIntegral Z]
    [Algebra K Z.functionField] (i : Z ⟶ pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
    [IsClosedImmersion i]
    [IsDominant (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))]
    [IsDominant (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))] :
    IntermediateField.adjoin K
      (Set.range (functionFieldMap
        (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))) ∪
       Set.range (functionFieldMap
        (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))))) = ⊤ := by
  obtain ⟨U, hUa, hU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  obtain ⟨V, hVa, hV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := genericPoint Y) (by trivial)
  exact chartField_adjoin K X Y i U V hUa hVa ⟨genericPoint X, hU⟩ ⟨genericPoint Y, hV⟩

end

end GroupActions
