import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic

/-!
# Torus Character Monomial Relations

Field-valued points of a finite-rank split torus separate its
characters, including finite products of characters. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {ν K : Type*} [Finite ν] [Field K] [IsAlgClosed K] [CharZero K]

local notation "M" => Multiplicative (ν →₀ ℤ)

omit [IsAlgClosed K] [CharZero K] in
private theorem splitTorus_coordinate_finiteType :
    Algebra.FiniteType K (MonoidAlgebra K M) := by
  have hfg : Monoid.FG M :=
    Group.fg_iff_monoid_fg.mp (AddGroup.fg_iff_mul_fg.mp
      (Module.Finite.iff_addGroup_fg.mp inferInstance))
  exact @MonoidAlgebra.finiteType_of_fg K M _ _ hfg

/-- Equality at every `K`-point of a split torus determines the
character itself. -/
theorem splitTorus_character_eq_of_point_eval_eq
    (α β : M)
    (h : ∀ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      t.ofConv (MonoidAlgebra.single α 1) =
        t.ofConv (MonoidAlgebra.single β 1)) :
    α = β := by
  let : Algebra.FiniteType K (MonoidAlgebra K M) :=
    splitTorus_coordinate_finiteType (K := K) (ν := ν)
  have heq : (MonoidAlgebra.single α (1 : K)) =
      MonoidAlgebra.single β (1 : K) := by
    apply TauCeti.eq_of_forall_algHom_apply_eq
      (k := K) (A := MonoidAlgebra K M) (K := K)
    intro f
    exact h (WithConv.toConv f)
  exact (MonoidAlgebra.single_left_injective (R := K) one_ne_zero) heq

/-- A finite monomial relation between character evaluations at every
split-torus point is the corresponding identity in its character
group. -/
theorem SplitTorus.character_prod_eq_of_point_eval_eq
    {κ : Type*} [Fintype κ]
    (χ : κ → M) (m : κ → ℕ) (β : M)
    (h : ∀ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      ∏ j, (t.ofConv (MonoidAlgebra.single (χ j) 1)) ^ (m j) =
        t.ofConv (MonoidAlgebra.single β 1)) :
    (∏ j, (χ j) ^ (m j)) = β := by
  have hsingle : (MonoidAlgebra.single (∏ j, χ j ^ m j) (1 : K)) =
      ∏ j, (MonoidAlgebra.single (χ j) (1 : K)) ^ m j := by
    change (MonoidAlgebra.of K M) (∏ j, χ j ^ m j) =
      ∏ j, ((MonoidAlgebra.of K M) (χ j)) ^ m j
    simp only [map_prod, map_pow]
  apply splitTorus_character_eq_of_point_eval_eq (K := K) (ν := ν)
  intro t
  rw [hsingle, map_prod]
  simpa only [map_pow] using h t

end ReductiveGroups
