import OrbitComplexity.GroupActions.Representations.ProjectiveAction
import OrbitComplexity.GroupActions.Representations.ChevalleyExterior

/-! # Projective stabilizers of closed affine subgroups

A finite exterior comodule contains a projective point with any prescribed closed
subgroup as stabilizer. Its algebraic projective action is induced by the comodule.
-/

noncomputable section
namespace GroupActions
open CategoryTheory AlgebraicGeometry TauCeti WithConv ReductiveGroups
universe u
variable {K H : Type u} [Field K] [CommRing H] [HopfAlgebra K H]

private theorem closed_points_eq (S : Subgroup (WithConv (H →ₐ[K] K)))
    (hc : IsClosed (S : Set (WithConv (H →ₐ[K] K)))) :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H)
      (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) = S := by
  obtain ⟨R, hR⟩ := (pointGroup_isClosed_iff (S : Set (WithConv (H →ₐ[K] K)))).mp hc
  apply le_antisymm
  · intro x hx
    change x ∈ (S : Set (WithConv (H →ₐ[K] K)))
    rw [hR]
    intro f hf
    have hvanish : f ∈ HopfIdeal.vanishingIdeal S := by
      apply (HopfIdeal.mem_vanishingIdeal S f).mpr
      intro g
      have hg : g.val ∈ (S : Set (WithConv (H →ₐ[K] K))) := g.property
      rw [hR] at hg
      exact hg f hf
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K H) (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) x).mp hx f hvanish
  · exact (HopfIdeal.le_vanishingIdeal_iff S (HopfIdeal.vanishingIdeal S)).mp le_rfl

variable [IsAlgClosed K] [CharZero K] [IsReduced H] [Algebra.FiniteType K H]

/-- Every closed affine subgroup is the stabilizer of a point in an algebraic projective action. -/
theorem exists_projective_stabilizer (S : Subgroup (WithConv (H →ₐ[K] K)))
    (hS : IsClosed (S : Set (WithConv (H →ₐ[K] K)))) :
    ∃ n : ℕ, ∃ μ : ModObj (affineVariety K H).toOver
        (projectiveVariety K (ULift.{u} (Fin n))).toOver,
      ∃ p : (projectiveVariety K (ULift.{u} (Fin n))).points,
        letI := μ
        ∀ g : WithConv (H →ₐ[K] K), affineGroupPointsMulEquiv K H g • p = p ↔ g ∈ S := by
  classical
  obtain ⟨M, hM⟩ := GroupActions.exists_finite_line_stabilizer S
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  obtain ⟨hfin, d, w, hw, hline⟩ := hM
  let : Module.Finite K M := hfin
  let W := ⋀[K]^d M
  let : Comodule K H W := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := M) d
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank K W))) K W :=
    (Module.finBasis K W).reindex Equiv.ulift.symm
  refine ⟨Module.finrank K W, comoduleProjectiveAction (H := H) b,
    comoduleProjectivePoint b w hw, ?_⟩
  intro g
  have ht := (comoduleProjective_stabilizer b w hw g).trans (hline g)
  rw [closed_points_eq S hS] at ht
  exact ht

end GroupActions
