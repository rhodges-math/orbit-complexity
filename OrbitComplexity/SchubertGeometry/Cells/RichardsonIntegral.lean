import OrbitComplexity.SchubertGeometry.Cells.RichardsonDensity
import OrbitComplexity.SchubertGeometry.Cells.RichardsonStrata
import OrbitComplexity.GroupActions.Varieties.FullDimension
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
import OrbitComplexity.GroupActions.Rosenlicht.ProductDimension
import OrbitComplexity.GroupActions.Representations.ProjectivePoints
import OrbitComplexity.GroupActions.MomentMaps.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Batteries.Tactic.Lint

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
/-! # Integral Richardson intersections

The Weyl flag of the lower endpoint belongs to both closed supports under Bruhat order.
Density of the open stratum then gives its nonemptiness, and preirreducibility gives
integrality of both reduced schemes. The dense immersion preserves their dimensions.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (a b : G.weylGroup)

private theorem closed_point (hab : WeylBruhatLE G.rootBase a b) :
    weylFlagPoint G a ∈ Set.range (Variety.mapPoints (richardsonInclusion G a b)) := by
  rw [richardson_points_range]
  constructor
  · rw [schubertVariety_points_cells]
    refine Set.mem_iUnion₂.mpr ⟨a, hab, ?_⟩
    rw [schubertCell_points_range]
    exact MulAction.mem_orbit_self _
  · rw [Variety.range_mapPoints, oppositeSchubertInclusion_range]
    apply subset_closure
    change (flagVariety G).pointMap (weylFlagPoint G a) ∈
      Set.range (oppositeSchubertCellInclusion G a).left
    change weylFlagPoint G a ∈ (flagVariety G).pointMap ⁻¹'
      Set.range (oppositeSchubertCellInclusion G a).left
    rw [← Variety.range_mapPoints, oppositeSchubertCell_points_range]
    exact MulAction.mem_orbit_self _

private theorem closed_nonempty (hab : WeylBruhatLE G.rootBase a b) :
    Nonempty (richardsonVariety G a b).scheme := by
  obtain ⟨x, _⟩ := closed_point G a b hab
  exact ⟨(richardsonVariety G a b).pointMap x⟩

private theorem open_nonempty (hab : WeylBruhatLE G.rootBase a b) :
    Nonempty (richardsonCell G a b).scheme := by
  let f : (richardsonCell G a b).scheme ⟶ (richardsonVariety G a b).scheme :=
    (richardsonCellToVariety G a b).left
  exact f.denseRange.nonempty_iff.mpr (closed_nonempty G a b hab)

private theorem closed_irreducible (hab : WeylBruhatLE G.rootBase a b) :
    IrreducibleSpace (richardsonVariety G a b).scheme := by
  exact ⟨closed_nonempty G a b hab⟩

private theorem open_irreducible (hab : WeylBruhatLE G.rootBase a b) :
    IrreducibleSpace (richardsonCell G a b).scheme := by
  exact ⟨open_nonempty G a b hab⟩

/-- A Richardson variety is integral when its lower endpoint is below its upper endpoint. -/
theorem richardsonVariety_integral (hab : WeylBruhatLE G.rootBase a b) :
    IsIntegral (richardsonVariety G a b).scheme := by
  have : IrreducibleSpace (richardsonVariety G a b).scheme := closed_irreducible G a b hab
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- An open Richardson stratum is integral under Bruhat order. -/
theorem richardsonCell_integral (hab : WeylBruhatLE G.rootBase a b) :
    IsIntegral (richardsonCell G a b).scheme := by
  have : IrreducibleSpace (richardsonCell G a b).scheme := open_irreducible G a b hab
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A Richardson variety is nonempty exactly under Bruhat order. -/
theorem richardsonVariety_nonempty_iff :
    Nonempty (richardsonVariety G a b).scheme ↔ WeylBruhatLE G.rootBase a b := by
  constructor
  · rintro ⟨x⟩
    obtain ⟨c, d, hac, hcd, hdb, _⟩ := richardsonVariety_cells_cover G a b x
    exact hac.trans (hcd.trans hdb)
  · exact closed_nonempty G a b

/-- An open Richardson stratum is nonempty exactly under Bruhat order. -/
theorem richardsonCell_nonempty_iff :
    Nonempty (richardsonCell G a b).scheme ↔ WeylBruhatLE G.rootBase a b := by
  constructor
  · rintro ⟨x⟩
    exact richardsonCell_order G a b x
  · exact open_nonempty G a b

/-- The open stratum and closed Richardson variety have equal dimension under Bruhat order. -/
theorem richardsonCell_dim_eq (hab : WeylBruhatLE G.rootBase a b) :
    (richardsonCell G a b).dim = (richardsonVariety G a b).dim := by
  have : IrreducibleSpace (richardsonCell G a b).scheme := open_irreducible G a b hab
  let f₀ : (richardsonCell G a b).scheme ⟶ (richardsonVariety G a b).scheme :=
    (richardsonCellToVariety G a b).left
  have hd := Variety.dim_closure_range_immersion (richardsonCellToVariety G a b)
  change topologicalKrullDim (closure (Set.range f₀)) = (richardsonCell G a b).dim at hd
  rw [f₀.denseRange.closure_eq] at hd
  exact hd.symm.trans
    (Homeomorph.Set.univ (richardsonVariety G a b).scheme).isHomeomorph.topologicalKrullDim_eq

attribute [local instance] MvPolynomial.gradedAlgebra

/-- One Richardson rational point meets every projective coordinate open that meets the image. -/
theorem richardson_full_coordinates (hab : WeylBruhatLE G.rootBase a b)
    {I : Type u} [Finite I]
    (f : (richardsonVariety G a b).toOver ⟶ (projectiveVariety K I).toOver) :
    ∃ x : (richardsonVariety G a b).points, ∀ i : I,
      (∃ y : (richardsonVariety G a b).points,
        (projectiveVariety K I).pointMap (Variety.mapPoints f y) ∈
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) →
      (projectiveVariety K I).pointMap (Variety.mapPoints f x) ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have : IsIntegral (richardsonVariety G a b).scheme := richardsonVariety_integral G a b hab
  let U : I → (richardsonVariety G a b).scheme.Opens := fun i =>
    f.left ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)
  let s : Finset (Set (richardsonVariety G a b).scheme) :=
    (Finset.univ.filter fun i => (U i : Set (richardsonVariety G a b).scheme).Nonempty).image
      (fun i => (U i : Set (richardsonVariety G a b).scheme))
  have hsOpen : ∀ V ∈ s, IsOpen V := by
    intro V hV
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hV
    exact (U i).isOpen
  have hsNonempty : ∀ V ∈ s,
      (Set.univ ∩ V : Set (richardsonVariety G a b).scheme).Nonempty := by
    intro V hV
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
    simpa only [Set.univ_inter] using (Finset.mem_filter.mp hi).2
  have hmeet : (⋂₀ (s : Set (Set (richardsonVariety G a b).scheme))).Nonempty := by
    have h := isIrreducible_iff_sInter.mp
      (IrreducibleSpace.isIrreducible_univ (richardsonVariety G a b).scheme)
      s hsOpen hsNonempty
    simpa only [Set.univ_inter] using h
  let W : (richardsonVariety G a b).scheme.Opens :=
    ⟨⋂₀ (s : Set (Set (richardsonVariety G a b).scheme)),
      s.finite_toSet.isOpen_sInter hsOpen⟩
  obtain ⟨x, hx⟩ := Variety.exists_point_mem_open (richardsonVariety G a b) W hmeet
  refine ⟨x, fun i ⟨y, hy⟩ => ?_⟩
  have hi : (U i : Set (richardsonVariety G a b).scheme).Nonempty := by
    refine ⟨(richardsonVariety G a b).pointMap y, ?_⟩
    change f.left ((richardsonVariety G a b).pointMap y) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)
    simpa only [Variety.pointMap_mapPoints] using hy
  have his : (U i : Set (richardsonVariety G a b).scheme) ∈ s :=
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  have hpoint := Set.mem_sInter.mp hx (U i : Set (richardsonVariety G a b).scheme) his
  change f.left ((richardsonVariety G a b).pointMap x) ∈
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) at hpoint
  simpa only [Variety.pointMap_mapPoints] using hpoint


omit [IsAlgClosed K] [CharZero K] in
private theorem coordinate_open_iff {I : Type u} [Finite I]
    (z : I → K) (hz : z ≠ 0) (i : I) :
    (projectiveVariety K I).pointMap (projectiveVectorPoint z hz) ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) ↔ z i ≠ 0 := by
  simpa only [MvPolynomial.eval_X] using
    (@projectiveVectorPoint_basicOpen K I inferInstance inferInstance z hz 1 Nat.zero_lt_one
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i))

end

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem polytope_mono_of_opens {I : Type} {E : Type*} [Finite I]
    [AddCommGroup E] [Module ℝ E] (weight : I → E) (p q : (projectiveVariety ℂ I).points)
    (h : ∀ i : I, (projectiveVariety ℂ I).pointMap p ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i) →
      (projectiveVariety ℂ I).pointMap q ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i)) :
    weightPolytope weight (projectivePointsEquiv.symm p) ⊆
      weightPolytope weight (projectivePointsEquiv.symm q) := by
  classical
  obtain ⟨rp, rfl⟩ := (projectivePointsEquiv (K := ℂ) (ι := I)).surjective p
  obtain ⟨rq, rfl⟩ := (projectivePointsEquiv (K := ℂ) (ι := I)).surjective q
  induction rp using Projectivization.ind with
  | _ vp hvp =>
    induction rq using Projectivization.ind with
    | _ vq hvq =>
      simp only [Equiv.symm_apply_apply, weightPolytope_mk]
      apply convexHull_mono
      apply Set.image_mono
      intro i hi
      exact (coordinate_open_iff vq hvq i).mp
        (h i ((coordinate_open_iff vp hvp i).mpr hi))

/-- One Richardson point has a weight polytope containing all the other image polytopes. -/
theorem richardson_maximal_weightPolytope (G : ReductiveGroupData ℂ) (a b : G.weylGroup)
    (hab : WeylBruhatLE G.rootBase a b) {I : Type} {E : Type*} [Finite I]
    [AddCommGroup E] [Module ℝ E]
    (f : (richardsonVariety G a b).toOver ⟶ (projectiveVariety ℂ I).toOver) (weight : I → E) :
    ∃ x : (richardsonVariety G a b).points,
      (∀ i : I, (∃ y : (richardsonVariety G a b).points,
        (projectiveVariety ℂ I).pointMap (Variety.mapPoints f y) ∈
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i)) →
        (projectiveVariety ℂ I).pointMap (Variety.mapPoints f x) ∈
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i)) ∧
      ∀ y : (richardsonVariety G a b).points,
        weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints f y)) ⊆
          weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints f x)) := by
  have hFull := @richardson_full_coordinates ℂ inferInstance inferInstance inferInstance
    G a b hab I inferInstance f
  obtain ⟨x, hx⟩ := hFull
  refine ⟨x, hx, fun y => ?_⟩
  exact polytope_mono_of_opens weight (Variety.mapPoints f y) (Variety.mapPoints f x)
    (fun i hy => hx i ⟨y, hy⟩)

end SchubertGeometry
