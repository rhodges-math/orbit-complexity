import OrbitComplexity.GroupActions.Varieties.AffineSchemeFibres
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-! # Generic fibre dimension for varieties

Finitely many affine charts of the source admit a common nonempty open part of an affine
base where their fibre dimension formulas hold. Their fibres cover the whole fibre, whose
dimension is the largest chart dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

private theorem finiteAffineCover_nonempty (X : Scheme.{u}) [CompactSpace X]
    (i : X.affineCover.finiteSubcover.I₀) : Nonempty (X.affineCover.finiteSubcover.X i) := by
  obtain ⟨z, hz⟩ := X.affineCover.covers i.1
  exact ⟨z⟩

/-- For a dominant morphism to an integral affine variety, the dimension formula holds
over a nonempty open part of the target. -/
theorem exists_open_dim_add_of_affine {K : Type u} [Field K]
    (X Y : GroupActions.Variety K) [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme]
    [IsAffine Y.scheme] (f : X.toOver ⟶ Y.toOver) [IsDominant f.left] :
    ∃ V : Y.scheme.Opens, (V : Set Y.scheme).Nonempty ∧ ∀ y ∈ V,
      X.dim = Y.dim + topologicalKrullDim (f.left.fiber y) := by
  classical
  let C := X.scheme.affineCover.finiteSubcover
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  have hn (i : C.I₀) : Nonempty (C.X i) := finiteAffineCover_nonempty X.scheme i
  have hd (i : C.I₀) : topologicalKrullDim (C.X i) = X.dim := by
    let := hn i
    exact (C.f i).isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (X.open_dim (C.f i).opensRange (Set.range_nonempty (C.f i)))
  have hl (i : C.I₀) : ∃ V : Y.scheme.Opens, (V : Set Y.scheme).Nonempty ∧
      ∀ y ∈ V, topologicalKrullDim (C.X i) = Y.dim +
        topologicalKrullDim ((C.f i ≫ f.left).fiber y) := by
    let := hn i
    have : IsIntegral (C.X i) := isIntegral_of_isOpenImmersion (C.f i)
    have : IsDominant (C.f i) :=
      ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (C.f i) (C.f i).isOpenEmbedding.isOpenMap⟩
    exact exists_open_dim_add_affine K (C.f i ≫ X.toSpec) Y.toSpec (C.f i ≫ f.left)
      (by
        rw [Category.assoc]
        exact congrArg (fun g ↦ C.f i ≫ g)
          (show f.left ≫ Y.toSpec = X.toSpec from f.w))
  choose V hV hdim using hl
  let W : Y.scheme.Opens :=
    ⟨⋂ i, (V i : Set Y.scheme), isOpen_iInter_of_finite fun i ↦ (V i).isOpen⟩
  refine ⟨W, ?_, ?_⟩
  · refine ⟨genericPoint Y.scheme, Set.mem_iInter.mpr fun i ↦ ?_⟩
    exact ((genericPoint_spec Y.scheme).mem_open_set_iff (V i).isOpen).mpr
      (by simpa only [Set.univ_inter] using hV i)
  · intro y hy
    have : Nonempty C.I₀ := by
      obtain ⟨i, z, hz⟩ := C.exists_eq (Classical.choice (inferInstance : Nonempty X.scheme))
      exact ⟨i⟩
    have hfibre : topologicalKrullDim (f.left.fiber y) =
        ⨆ i : C.I₀, topologicalKrullDim ((C.f i ≫ f.left).fiber y) :=
      TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_iSup_openCover
        (Scheme.Pullback.openCoverOfLeft C f.left (Y.scheme.fromSpecResidueField y))
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
      (f := fun i : C.I₀ ↦ topologicalKrullDim ((C.f i ≫ f.left).fiber y))
    have h := hdim i y ((Set.mem_iInter.mp hy) i)
    rw [hd i, hi.trans hfibre.symm] at h
    exact h

end

end GroupActions.Variety
