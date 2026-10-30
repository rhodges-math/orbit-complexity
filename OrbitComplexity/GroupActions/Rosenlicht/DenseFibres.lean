import OrbitComplexity.GroupActions.Varieties.RestrictedMorphisms
import OrbitComplexity.GroupActions.Rosenlicht.AffineFibreDensity

/-!
# Generic density of open subsets in variety fibres
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

/-- A nonempty open subset of an integral variety is dense in all fibres over
some nonempty open subset of an integral affine base. -/
theorem exists_open_dense_fibres_affine_base {K : Type u} [Field K]
    (Y X : GroupActions.Variety K) [IrreducibleSpace Y.scheme]
    [IrreducibleSpace X.scheme] [IsAffine X.scheme]
    (f : Y.toOver ⟶ X.toOver) (U : Y.scheme.Opens) (hU : (U : Set Y.scheme).Nonempty) :
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧ ∀ x ∈ V,
      Dense {z : f.left ⁻¹' {x} | z.val ∈ U} := by
  classical
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  let C := Y.scheme.affineCover.finiteSubcover
  have hn (i : C.I₀) : Nonempty (C.X i) := by
    obtain ⟨z, hz⟩ := Y.scheme.affineCover.covers i.1
    exact ⟨z⟩
  let A (i : C.I₀) : GroupActions.Variety K := by
    let _ := hn i
    have : IsIntegral (C.X i) := isIntegral_of_isOpenImmersion (C.f i)
    exact { scheme := C.X i, toSpec := C.f i ≫ Y.toSpec }
  let g (i : C.I₀) : (A i).toOver ⟶ X.toOver :=
    Over.homMk (C.f i ≫ f.left) (by
      change (C.f i ≫ f.left) ≫ X.toSpec = C.f i ≫ Y.toSpec
      rw [Category.assoc]
      exact congrArg (fun h ↦ C.f i ≫ h) f.w)
  have hl (i : C.I₀) : ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧
      ∀ x ∈ V, Dense {z : (g i).left ⁻¹' {x} | z.val ∈ (C.f i) ⁻¹ᵁ U} := by
    let _ := hn i
    have : IsIntegral (A i).scheme := isIntegral_of_isOpenImmersion (C.f i)
    have : IsAffine (A i).scheme := inferInstanceAs (IsAffine (C.X i))
    have : IsDominant (C.f i) :=
      ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (C.f i) (C.f i).isOpenEmbedding.isOpenMap⟩
    exact exists_open_dense_fibres_affine (A i) X (g i) ((C.f i) ⁻¹ᵁ U)
      ((C.f i).denseRange.exists_mem_open U.isOpen hU)
  choose V hV hD using hl
  let W : X.scheme.Opens :=
    ⟨⋂ i, (V i : Set X.scheme), isOpen_iInter_of_finite fun i ↦ (V i).isOpen⟩
  refine ⟨W, ?_, ?_⟩
  · refine ⟨genericPoint X.scheme, Set.mem_iInter.mpr fun i ↦ ?_⟩
    exact ((genericPoint_spec X.scheme).mem_open_set_iff (V i).isOpen).mpr
      (by simpa only [Set.univ_inter] using hV i)
  · intro x hx
    apply dense_iff_inter_open.mpr
    intro T hT ⟨z, hz⟩
    obtain ⟨i, a, ha⟩ := C.exists_eq z.val
    have ha' : (g i).left a = x := by
      change f.left (C.f i a) = x
      rw [ha]
      exact z.property
    let j : ((g i).left ⁻¹' {x}) → (f.left ⁻¹' {x}) :=
      fun a ↦ ⟨C.f i a.val, a.property⟩
    have hj : Continuous j :=
      ((C.f i).continuous.comp continuous_subtype_val).subtype_mk _
    have hz' : j ⟨a, ha'⟩ = z := Subtype.ext ha
    obtain ⟨a', haU, haT⟩ := (hD i x (Set.mem_iInter.mp hx i)).exists_mem_open
      (hT.preimage hj) ⟨⟨a, ha'⟩, by
        change j ⟨a, ha'⟩ ∈ T
        rw [hz']
        exact hz⟩
    exact ⟨j a', haT, haU⟩

end

end GroupActions.Variety

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

private def topologicalRestriction {Y X : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens) :
    (f ⁻¹' (V : Set X)) → V := fun z ↦ ⟨f z.val, z.property⟩

private def denseRestrictHomeomorph {Y X : Scheme.{u}}
    (f : Y ⟶ X) (V : X.Opens) (x : V) :
    ((topologicalRestriction f V) ⁻¹' {x}) ≃ₜ (f ⁻¹' {(x : X)}) where
  toEquiv :=
    { toFun := fun z ↦ ⟨z.val.val, congrArg Subtype.val z.property⟩
      invFun := fun z ↦ ⟨⟨z.val, by
        change f z.val ∈ V
        rw [show f z.val = (x : X) from z.property]
        exact x.property⟩, Subtype.ext z.property⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl }
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

namespace Variety

/-- Every nonempty open subset of an integral variety is dense in all fibres
over a nonempty open subset of an integral base variety. -/
theorem exists_open_dense_fibres {K : Type u} [Field K]
    (Y X : GroupActions.Variety K) [IrreducibleSpace Y.scheme]
    [IrreducibleSpace X.scheme] (f : Y.toOver ⟶ X.toOver)
    (U : Y.scheme.Opens) (hU : (U : Set Y.scheme).Nonempty) :
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧ ∀ x ∈ V,
      Dense {z : f.left ⁻¹' {x} | z.val ∈ U} := by
  let g : Y.scheme ⟶ X.scheme := f.left
  obtain ⟨V₀, hV₀, hηV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show g (genericPoint Y.scheme) ∈ (⊤ : X.scheme.Opens) from trivial)
  have hVne : (V₀ : Set X.scheme).Nonempty := ⟨_, hηV⟩
  have hYne : ((g ⁻¹ᵁ V₀) : Set Y.scheme).Nonempty := ⟨_, hηV⟩
  let Y' := Y.openSubvariety (g ⁻¹ᵁ V₀)
  let X' := X.openSubvariety V₀
  have : Nonempty ((g ⁻¹ᵁ V₀) : Scheme) := ⟨⟨_, hηV⟩⟩
  have : Nonempty (V₀ : Scheme) := ⟨⟨_, hηV⟩⟩
  have : IrreducibleSpace Y'.scheme := (g ⁻¹ᵁ V₀).ι.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace X'.scheme := V₀.ι.isOpenEmbedding.irreducibleSpace
  have : IsAffine X'.scheme := hV₀
  let f' := restrictHom f V₀
  let U' : Y'.scheme.Opens := (g ⁻¹ᵁ V₀).ι ⁻¹ᵁ U
  have hηU : genericPoint Y.scheme ∈ U :=
    ((genericPoint_spec Y.scheme).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  have hU' : (U' : Set Y'.scheme).Nonempty := ⟨⟨_, hηV⟩, hηU⟩
  obtain ⟨W, hW, hD⟩ := exists_open_dense_fibres_affine_base Y' X' f' U' hU'
  refine ⟨V₀.ι ''ᵁ W, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hW
    exact ⟨V₀.ι x, V₀.ι.apply_mem_image_iff.mpr hx⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let e := denseRestrictHomeomorph g V₀ y
    have hf' : (f'.left : (g ⁻¹' (V₀ : Set X.scheme)) → V₀) =
        topologicalRestriction g V₀ := by
      funext z
      apply Subtype.ext
      exact morphismRestrict_base_coe g V₀ z
    have hyD := hD y hy
    change Dense {z : (f'.left : (g ⁻¹' (V₀ : Set X.scheme)) → V₀) ⁻¹' {y} |
      z.val.val ∈ U} at hyD
    rw [hf'] at hyD
    have hi := e.surjective.denseRange.dense_image e.continuous hyD
    apply hi.mono
    rintro z ⟨a, ha, rfl⟩
    exact ha

end Variety

end

end GroupActions
