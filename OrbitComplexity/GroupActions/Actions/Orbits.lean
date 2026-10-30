import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.GroupActions.Varieties.FiniteDimension
import Batteries.Tactic.Lint

/-! # Orbit closures and orbit dimensions

The closure of a rational-point orbit is taken inside the underlying scheme. It is the
closure of the image of the orbit morphism, and its Krull dimension defines orbit dimension.

## Main definitions

* `GroupActions.orbitClosure`: the scheme closure of a rational-point orbit.
* `GroupActions.orbitDim`: the dimension of an orbit.
* `GroupActions.orbitNatDim`: orbit dimension as a natural number.
* `GroupActions.orbitCodim`: the integer codimension of an orbit.

## Main results

* `GroupActions.orbitClosure_eq`: the orbit closure is the closure of the orbit morphism's image.
* `GroupActions.orbitDim_le`: orbit dimension is bounded by the variety's dimension.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- The closure of an orbit of rational points in the underlying scheme. -/
def orbitClosure (x : X.points) : Set X.scheme := X.pointClosure (MulAction.orbit H.points x)

/-- Translation by a rational group element preserves the scheme orbit closure. -/
theorem orbitClosure_smul_mem (x y : X.points) (t : H.points)
    (hy : X.pointMap y ∈ orbitClosure H X x) :
    X.pointMap (t • y) ∈ orbitClosure H X x := by
  let f := Variety.translateMorphism H X t
  let S : Set X.scheme := X.pointMap '' MulAction.orbit H.points x
  have hpoint (z : X.points) : X.pointMap (t • z) = f.left (X.pointMap z) := by
    calc
      _ = X.pointMap (Variety.mapPoints f z) :=
        congrArg X.pointMap (Variety.mapPoints_translateMorphism H X t z).symm
      _ = _ := Variety.pointMap_mapPoints f z
  have hpreserve : f.left '' S ⊆ S := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨t • z, ?_, hpoint z⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    exact MulAction.mem_orbit_iff.mpr ⟨t * g, mul_smul t g x⟩
  change X.pointMap y ∈ closure S at hy
  change X.pointMap (t • y) ∈ closure S
  rw [hpoint y]
  exact closure_mono hpreserve
    ((image_closure_subset_closure_image f.left.continuous)
      (Set.mem_image_of_mem f.left hy))

/-- The dimension of an orbit is the dimension of its scheme closure. -/
def orbitDim (x : X.points) : WithBot ℕ∞ := X.subsetDim (MulAction.orbit H.points x)

/-- Orbit dimension is bounded by the dimension of the ambient variety. -/
theorem orbitDim_le (x : X.points) : orbitDim H X x ≤ X.dim :=
  X.subsetDim_le (MulAction.orbit H.points x)

/-- The dimension of an orbit is nonnegative. -/
theorem orbitDim_nonneg (x : X.points) : 0 ≤ orbitDim H X x :=
  X.subsetDim_nonneg (MulAction.nonempty_orbit x)

/-- The dimension of an orbit is different from bottom. -/
theorem orbitDim_ne_bot (x : X.points) : orbitDim H X x ≠ ⊥ := by
  intro h
  exact not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) (h ▸ orbitDim_nonneg H X x)

/-- The orbit closure is the closure of the image of the orbit morphism. -/
theorem orbitClosure_eq [IsAlgClosed K] (x : X.points) :
    orbitClosure H X x = closure (Set.range (Variety.orbitMorphism H X x).left) := by
  rw [orbitClosure, ← Variety.range_orbitMorphism H X x]
  exact H.pointClosure_range (Variety.orbitMorphism H X x)

/-- The natural-number dimension of an orbit. -/
def orbitNatDim (x : X.points) : ℕ := ((orbitDim H X x).unbotD 0).toNat

/-- The natural-number orbit dimension equals its Krull dimension after casting. -/
theorem orbitNatDim_cast (x : X.points) :
    (orbitNatDim H X x : WithBot ℕ∞) = orbitDim H X x :=
  Variety.natCast_unbotD_toNat _ (orbitDim_ne_bot H X x)
    (X.subsetDim_ne_top (MulAction.orbit H.points x))

/-- Natural-number orbit dimension is bounded by the ambient dimension. -/
theorem orbitNatDim_le (x : X.points) : orbitNatDim H X x ≤ X.natDim := by
  have : Nonempty X.scheme := ⟨X.pointMap x⟩
  have h : (orbitNatDim H X x : WithBot ℕ∞) ≤ (X.natDim : WithBot ℕ∞) := by
    rw [orbitNatDim_cast, X.natDim_cast]
    exact orbitDim_le H X x
  exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp h)

/-- The integer codimension of an orbit in its ambient variety. -/
def orbitCodim (x : X.points) : ℤ := (X.natDim : ℤ) - (orbitNatDim H X x : ℤ)

/-- Orbit codimension is nonnegative. -/
theorem orbitCodim_nonneg (x : X.points) : 0 ≤ orbitCodim H X x :=
  sub_nonneg.mpr (Int.ofNat_le.mpr (orbitNatDim_le H X x))

end

end GroupActions
