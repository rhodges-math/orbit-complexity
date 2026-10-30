import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates

/-!
# Root support factorization

Disjoint closed positive-root supports give a unique ordered factorization of rational
points. The factors lie in the closed root-subgroup coordinate quotients.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem mem_rootSubsetPoints_iff (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (g : G.unipotentPoints) :
    g.val ∈ G.rootSubsetPoints R hR ↔ g ∈ borelRootSubsetPoints G.borelIdeal G.isBorel
      G.torusSplit G.split_surjective G.borelRootBasis (G.rootCharacters R) := by
  have he := congrArg (fun H : Subgroup G.points => g.val ∈ H) (G.rootSubsetPoints_eq R hR)
  constructor
  · intro hg
    obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp (he.mp hg)
    have hueq : u = g := Subtype.ext heq
    exact hueq ▸ hu
  · intro hg
    exact he.mpr (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

/-- Disjoint closed root supports give unique multiplication factors in the ambient group. -/
theorem rootSubsetPoints_existsUnique_mul
    (R R₁ R₂ : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R)
    (hR₁ : IsPositiveRootClosed G.rootBase R₁) (hR₂ : IsPositiveRootClosed G.rootBase R₂)
    (hunion : R = R₁ ∪ R₂) (hdisj : Disjoint R₁ R₂)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    ∃! p : G.points × G.points,
      p.1 ∈ G.rootSubsetPoints R₁ hR₁ ∧ p.2 ∈ G.rootSubsetPoints R₂ hR₂ ∧ p.1 * p.2 = g := by
  let u : G.unipotentPoints := ⟨g, G.rootSubsetPoints_le_unipotent R hR hg⟩
  have hu := (G.mem_rootSubsetPoints_iff R hR u).mp hg
  have hchars : G.rootCharacters R = G.rootCharacters R₁ ∪ G.rootCharacters R₂ := by
    ext i
    change _ ∈ R ↔ _ ∈ R₁ ∨ _ ∈ R₂
    rw [hunion]
    rfl
  have hdchars : Disjoint (G.rootCharacters R₁) (G.rootCharacters R₂) := by
    rw [Set.disjoint_left]
    intro i hi₁ hi₂
    exact Set.disjoint_left.mp hdisj hi₁ hi₂
  obtain ⟨q, ⟨hq₁, hq₂, hqprod⟩, hq⟩ := borelRootSubsetPoints_existsUnique_mul
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps G.borelRootBasis
    G.borelRootBasis_tangent G.borelRootMaps_weight (G.rootCharacters_closed R hR)
    (G.rootCharacters_closed R₁ hR₁) (G.rootCharacters_closed R₂ hR₂) hchars hdchars u hu
  refine ⟨(q.1.val, q.2.val), ⟨(G.mem_rootSubsetPoints_iff R₁ hR₁ q.1).mpr hq₁,
    (G.mem_rootSubsetPoints_iff R₂ hR₂ q.2).mpr hq₂, congrArg Subtype.val hqprod⟩, ?_⟩
  rintro ⟨g₁, g₂⟩ ⟨hg₁, hg₂, hprod⟩
  let u₁ : G.unipotentPoints := ⟨g₁, G.rootSubsetPoints_le_unipotent R₁ hR₁ hg₁⟩
  let u₂ : G.unipotentPoints := ⟨g₂, G.rootSubsetPoints_le_unipotent R₂ hR₂ hg₂⟩
  have heq : (u₁, u₂) = q := hq (u₁, u₂)
    ⟨(G.mem_rootSubsetPoints_iff R₁ hR₁ u₁).mp hg₁,
      (G.mem_rootSubsetPoints_iff R₂ hR₂ u₂).mp hg₂, Subtype.ext hprod⟩
  exact Prod.ext (congrArg (fun v : G.unipotentPoints × G.unipotentPoints => v.1.val) heq)
    (congrArg (fun v : G.unipotentPoints × G.unipotentPoints => v.2.val) heq)

end ReductiveGroups.ReductiveGroupData
