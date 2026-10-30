import OrbitComplexity.GroupActions.Representations.ChevalleyLine
import OrbitComplexity.GroupActions.Representations.ExteriorActions

/-! # Lines in exterior comodules

A finite regular subcomodule and one of its exterior powers contain a line with the
stabilizer defined by a given subgroup's vanishing ideal. The exterior action is induced
by its comodule structure.
-/

noncomputable section
namespace GroupActions
open TauCeti WithConv
universe u v
variable {K : Type u} {H : Type v} [Field K] [CharZero K] [CommRing H]
  [HopfAlgebra K H] [Algebra.FiniteType K H]

/-- A finite exterior comodule contains a line with the prescribed closed stabilizer. -/
theorem exists_finite_line_stabilizer (S : Subgroup (WithConv (H →ₐ[K] K))) :
  ∃ M : Subcomodule K H H,
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
    Module.Finite K M ∧
      ∃ (d : ℕ) (w : ⋀[K]^d M), w ≠ 0 ∧
        letI := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := M) d
        ∀ g : WithConv (H →ₐ[K] K),
          (Submodule.span K {w}).map
              (Comodule.basePointsRepresentation (R := K) (H := H) (⋀[K]^d M) g) =
            Submodule.span K {w} ↔
              g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H)
                (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) := by
  obtain ⟨M, hM⟩ := GroupActions.exists_comodule_line_stabilizer S
  refine ⟨M, ?_⟩
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  obtain ⟨hfin, d, w, hw, hS⟩ := hM
  refine ⟨hfin, d, w, hw, ?_⟩
  let := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := M) d
  intro g
  rw [GroupActions.exteriorPower_basePoints]
  exact hS g

end GroupActions
