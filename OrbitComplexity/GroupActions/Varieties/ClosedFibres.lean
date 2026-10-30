import OrbitComplexity.GroupActions.Varieties.ClosedAffineFibres
import OrbitComplexity.GroupActions.Varieties.RestrictedFibreDimension
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-! # Lower bounds for fibres at closed points

A nonempty affine source chart around a closed point has the dimension of its irreducible
ambient variety. The affine fibre inequality and monotonicity under restriction therefore
give the dimension lower bound in the whole fibre. Rational points are closed because
they are sections of separated structure morphisms.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X Y : GroupActions.Variety K)
  [IrreducibleSpace X.scheme]

/-- A fibre under a closed point of an irreducible source has the dimension lower bound. -/
theorem dim_le_add_fiber_of_closed (f : X.scheme ⟶ Y.scheme) (x : X.scheme)
    (hx : IsClosed ({x} : Set X.scheme)) :
    X.dim ≤ Y.dim + topologicalKrullDim (f.fiber (f x)) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.scheme.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : Nonempty (U : Scheme) := ⟨⟨x, hxU⟩⟩
  have : IsIntegral (U : Scheme) := isIntegral_of_isOpenImmersion U.ι
  have : IsAffine (U : Scheme) := hU
  have : IsAffine (V : Scheme) := hV
  let xU : U := ⟨x, hxU⟩
  let g := f.resLE V U hUV
  have hclosed : IsClosed ({xU} : Set U) := by
    convert hx.preimage U.ι.continuous using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact Subtype.ext_iff
  have h := GroupActions.dim_le_add_fiber_affine K
    (U.ι ≫ X.toSpec) (V.ι ≫ Y.toSpec) g xU hclosed
  have hdU : topologicalKrullDim (U : Scheme) = X.dim := X.open_dim U ⟨x, hxU⟩
  have hdV : topologicalKrullDim (V : Scheme) ≤ Y.dim :=
    IsInducing.subtypeVal.topologicalKrullDim_le
  have hfib := GroupActions.fibre_dim_resLE_le f V U hUV (g xU)
  have hbase : (g xU).1 = f x :=
    Scheme.Hom.coe_resLE_apply f hUV xU
  change topologicalKrullDim (g.fiber (g xU)) ≤
    topologicalKrullDim (f.fiber (g xU).1) at hfib
  rw [hbase] at hfib
  rw [hdU] at h
  exact h.trans (add_le_add hdV hfib)

/-- A fibre under a rational point of an irreducible source has the dimension lower bound. -/
theorem dim_le_add_fiber (f : X.toOver ⟶ Y.toOver) (x : X.points) :
    X.dim ≤ Y.dim +
      topologicalKrullDim (f.left.fiber (Y.pointMap (mapPoints f x))) := by
  have : IsClosedImmersion x.val := by
    have : IsClosedImmersion (x.val ≫ X.toSpec) := by
      rw [x.property]
      infer_instance
    exact IsClosedImmersion.of_comp x.val X.toSpec
  have hrange : Set.range x.val = {X.pointMap x} := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact congrArg x.val (Subsingleton.elim p (IsLocalRing.closedPoint K))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint K, rfl⟩
  have hx : IsClosed ({X.pointMap x} : Set X.scheme) := by
    rw [← hrange]
    exact x.val.isClosedEmbedding.isClosed_range
  let g : X.scheme ⟶ Y.scheme := f.left
  rw [pointMap_mapPoints]
  change X.dim ≤ Y.dim + topologicalKrullDim (g.fiber (g (X.pointMap x)))
  exact dim_le_add_fiber_of_closed X Y g (X.pointMap x) hx

end

end GroupActions.Variety
