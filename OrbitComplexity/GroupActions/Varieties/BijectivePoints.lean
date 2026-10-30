import OrbitComplexity.GroupActions.Varieties.GenericBaseFibres
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Rosenlicht.ProductDimension

/-! # Dimension and bijective rational points

An injective rational-point map has singleton fibres at its rational image.
A surjective rational-point map is surjective on schemes, and the generic fibre
dimension formula proves dimension invariance for a bijective point map.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
namespace GroupActions.Variety
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Variety K}

private theorem fibre_eq_singleton (f : X.toOver ⟶ Y.toOver)
    (hf : Function.Injective (mapPoints f)) (x : X.points) :
    f.left ⁻¹' {Y.pointMap (mapPoints f x)} = {X.pointMap x} := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  have hc : IsClosed (f.left ⁻¹' {Y.pointMap (mapPoints f x)}) :=
    (Y.pointsEquivClosedPoints (mapPoints f x)).property.preimage f.left.continuous
  have he : (f.left ⁻¹' {Y.pointMap (mapPoints f x)}) ∩ closedPoints X.scheme =
      {X.pointMap x} := by
    ext p
    constructor
    · rintro ⟨hp, hpc⟩
      obtain ⟨a, ha⟩ := X.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
      have hpa : X.pointMap a = p := congrArg Subtype.val ha
      have hax : mapPoints f a = mapPoints f x := by
        apply Y.pointMap_injective
        rw [pointMap_mapPoints, hpa]
        exact hp
      rw [hf hax] at hpa
      exact hpa.symm
    · rintro rfl
      exact ⟨rfl, (X.pointsEquivClosedPoints x).property⟩
  have hclosure : closure ((f.left ⁻¹' {Y.pointMap (mapPoints f x)}) ∩
      closedPoints X.scheme) = f.left ⁻¹' {Y.pointMap (mapPoints f x)} :=
    @closure_inter_closedPoints X.scheme inferInstance inferInstance _ hc
  rw [he] at hclosure
  exact hclosure.symm.trans (X.pointsEquivClosedPoints x).property.closure_eq

omit [IsAlgClosed K] in
private theorem singleton_dim (x : X.scheme) :
    topologicalKrullDim ({x} : Set X.scheme) = 0 := by
  have : IrreducibleSpace ({x} : Set X.scheme) :=
    Subtype.irreducibleSpace isIrreducible_singleton
  have : Nonempty (IrreducibleCloseds ({x} : Set X.scheme)) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

/-- An injective map on rational points has zero-dimensional fibres at its rational image. -/
theorem fibre_dim_of_injective_points (f : X.toOver ⟶ Y.toOver)
    (hf : Function.Injective (mapPoints f)) (x : X.points) :
    topologicalKrullDim (f.left.fiber (Y.pointMap (mapPoints f x))) = 0 := by
  have he := ((f.left.fiberHomeo (Y.pointMap (mapPoints f x))).trans
    (Homeomorph.setCongr (fibre_eq_singleton f hf x))).isHomeomorph.topologicalKrullDim_eq
  exact he.trans (singleton_dim (X.pointMap x))

/-- A surjective rational-point morphism from an irreducible variety has irreducible target. -/
theorem irreducible_of_surjective_points [IrreducibleSpace X.scheme]
    (f : X.toOver ⟶ Y.toOver) (hf : Function.Surjective (mapPoints f)) :
    IrreducibleSpace Y.scheme := by
  have hr := range_subset_of_mapPoints (𝟙 Y.toOver) f (by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hf (mapPoints (𝟙 Y.toOver) y)
    exact ⟨x, hx⟩)
  have hs : Function.Surjective (f.left : X.scheme → Y.scheme) := by
    intro y
    exact hr ⟨y, rfl⟩
  exact Function.Surjective.irreducibleSpace (X := X.scheme) (Y := Y.scheme)
    (f := (f.left : X.scheme → Y.scheme)) f.left.continuous hs

/-- A bijective rational-point morphism from an irreducible variety preserves dimension. -/
theorem dim_eq_of_bijective_points [IrreducibleSpace X.scheme]
    (f : X.toOver ⟶ Y.toOver) (hf : Function.Bijective (mapPoints f)) : X.dim = Y.dim := by
  have : IrreducibleSpace Y.scheme := irreducible_of_surjective_points f hf.2
  have hs : Function.Surjective (f.left : X.scheme → Y.scheme) := by
    have hr := range_subset_of_mapPoints (𝟙 Y.toOver) f (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hf.2 (mapPoints (𝟙 Y.toOver) y)
      exact ⟨x, hx⟩)
    intro y
    exact hr ⟨y, rfl⟩
  have : Surjective f.left := ⟨hs⟩
  obtain ⟨V, hV, hd⟩ := exists_open_dim_add X Y f
  obtain ⟨y, hy⟩ := exists_point_mem_open Y V hV
  obtain ⟨x, rfl⟩ := hf.2 y
  have he := hd _ hy
  rw [fibre_dim_of_injective_points f hf.1 x, add_zero] at he
  exact he

end GroupActions.Variety
