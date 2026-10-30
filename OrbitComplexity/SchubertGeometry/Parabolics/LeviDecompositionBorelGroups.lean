import OrbitComplexity.SchubertGeometry.Levi.Dimension
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SemidirectProduct

/-! # Semidirect factors in Levi Borel point groups

The torus normalizes the positive subsystem root group. Their intersection is
trivial and their multiplication covers the Levi Borel subgroup.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups TauCeti
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private abbrev roots (I : Set G.rootBase.support) : Subgroup G.points :=
  G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
    (LeviRootSpan.isPositiveRootClosed G.rootBase I)

private theorem roots_le (I : Set G.rootBase.support) : roots G I ≤ G.leviBorelPoints I :=
  G.rootSubsetPoints_le_leviBorel I _ _ (fun _ h => h)

private theorem borel_normalizes (I : Set G.rootBase.support) :
    G.leviBorelPoints I ≤ Subgroup.normalizer (roots G I : Set G.points) := by
  let N := Subgroup.normalizer (roots G I : Set G.points)
  intro b hb
  obtain ⟨t, ht, u, hu, he⟩ := G.leviBorel_exists_torus_mul I b hb
  have htN : t ∈ N := G.torusPoints_le_rootNormalizer _
    (LeviRootSpan.isPositiveRootClosed G.rootBase I) ht
  have huN : u ∈ N := (roots G I).le_normalizer hu
  exact he ▸ N.mul_mem htN huN

/-- The chosen torus as a subgroup of the Levi Borel point group. -/
abbrev torusInLeviBorel (I : Set G.rootBase.support) : Subgroup (G.leviBorelPoints I) :=
  G.torusPoints.subgroupOf (G.leviBorelPoints I)

/-- The positive subsystem root group inside the Levi Borel point group. -/
abbrev rootsInLeviBorel (I : Set G.rootBase.support) : Subgroup (G.leviBorelPoints I) :=
  (G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
    (LeviRootSpan.isPositiveRootClosed G.rootBase I)).subgroupOf (G.leviBorelPoints I)

/-- The positive subsystem root group is normal in the Levi Borel point group. -/
instance rootsInLeviBorel_normal (I : Set G.rootBase.support) :
    (rootsInLeviBorel G I).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (borel_normalizes G I)

/-- The torus and positive subsystem roots are complementary in the Levi Borel group. -/
theorem leviBorelComplement (I : Set G.rootBase.support) :
    (torusInLeviBorel G I).IsComplement' (rootsInLeviBorel G I) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    apply eq_bot_iff.mpr
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact BorelRootUnipotent.torus_intersection_eq_one G.torusIdeal G.borelIdeal
      G.isBorel G.torusSplit G.split_surjective G.split_eq_zero (CommAlgCat.of K K)
      x.val hx.1 (G.rootSubsetPoints_le_unipotent _ _ hx.2)
  · apply Set.eq_univ_of_forall
    intro b
    obtain ⟨t, ht, u, hu, he⟩ := G.leviBorel_exists_torus_mul I b.val b.property
    exact Set.mem_mul.mpr ⟨⟨t, G.torus_le_leviBorelPoints I ht⟩, ht,
      ⟨u, roots_le G I hu⟩, hu, Subtype.ext he⟩

/-- The Levi Borel group is the semidirect product of its positive roots and torus. -/
def leviBorelSemidirectIso (I : Set G.rootBase.support) :
    (rootsInLeviBorel G I) ⋊[
      ((rootsInLeviBorel G I).normalizerMonoidHom).comp (Subgroup.inclusion
        ((rootsInLeviBorel G I).normalizer_eq_top ▸ le_top))]
      (torusInLeviBorel G I) ≃* G.leviBorelPoints I :=
  SemidirectProduct.mulEquivSubgroup (leviBorelComplement G I).symm

end SchubertGeometry
