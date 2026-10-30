import OrbitComplexity.GroupActions.Varieties.RootOrderedProduct
import OrbitComplexity.SchubertGeometry.Cells.RootPoints
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Products of the inversion root subgroups

In any ordering, multiplication of the inversion-root parameters has image U_w
and gives a unique factorization of each of its points.
-/

open ReductiveGroups GroupActions SchubertGeometry
noncomputable section
namespace SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The inversion subgroup is the product of its root groups in every ordering,
with unique parameters for each point. -/
theorem schubertUnipotent_root_product (w : G.weylGroup)
    (l : List (G.inversionCharacters w)) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (schubertUnipotentPoints G w : Set G.points) =
      Set.range (fun a : G.inversionCharacters w → K =>
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
    ∀ g : G.points, g ∈ schubertUnipotentPoints G w →
      ∃! a : G.inversionCharacters w → K,
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod = g := by
  obtain ⟨hmem, huniq⟩ := rootSubset_ordered_product G
    (leftRootInversionIndices G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) l hl hall
  refine ⟨?_, huniq⟩
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, _⟩ := huniq g hg
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact hmem a

/-- Over the complex numbers, any ordering of the inversion root groups directly
spans the inversion subgroup. -/
theorem schubertUnipotent_root_complex (G : ReductiveGroupData ℂ) (w : G.weylGroup)
    (l : List (G.inversionCharacters w)) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (schubertUnipotentPoints G w : Set G.points) =
      Set.range (fun a : G.inversionCharacters w → ℂ =>
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
    ∀ g : G.points, g ∈ schubertUnipotentPoints G w →
      ∃! a : G.inversionCharacters w → ℂ,
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod = g :=
  schubertUnipotent_root_product G w l hl hall

end SchubertOrbits
