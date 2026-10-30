import OrbitComplexity.SchubertGeometry.Levi.Maps
import OrbitComplexity.SchubertGeometry.Levi.BorelInclusion
import OrbitComplexity.SchubertGeometry.Levi.Center
import OrbitComplexity.SchubertGeometry.Parabolics.CellStability
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTrivial
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # The Levi subgroup for an empty set of simple roots

The Levi and its Borel have the chosen torus as their point subgroup. The canonical
torus inclusions are isomorphisms of the reduced group varieties.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem iso_of_image {X Y Z : Variety K}
    (f : X.toOver ⟶ Y.toOver) (i : Y.toOver ⟶ Z.toOver)
    (j : X.toOver ⟶ Z.toOver) [IsPreimmersion i.left] [IsPreimmersion j.left]
    (hfac : f ≫ i = j)
    (h : Set.range (Variety.mapPoints j) = Set.range (Variety.mapPoints i)) :
    IsIso f := by
  let e := Variety.pointImageIso j i h
  have : Mono i := Over.mono_of_mono_left i
  have he : f = e.hom := (cancel_mono i).mp
    (hfac.trans (Variety.pointImageIso_hom_comp j i h).symm)
  rw [he]
  infer_instance

variable [CharZero K] (G : ReductiveGroupData K)

private theorem empty_roots : leviPositiveRoots G.rootBase ∅ = ∅ := by
  ext r
  simp [leviPositiveRoots]

private theorem empty_borel : G.leviBorelPoints ∅ = G.torusPoints := by
  apply le_antisymm _ (G.torus_le_leviBorelPoints ∅)
  intro b hb
  obtain ⟨t, ht, x, hx, he⟩ := G.leviBorel_exists_torus_mul ∅ b hb
  have hbot := (G.rootSubsetPoints_eq_bot_iff (leviPositiveRoots G.rootBase ∅)
    (LeviRootSpan.isPositiveRootClosed G.rootBase ∅) (fun _ h => h.1)).mpr (empty_roots G)
  rw [hbot, Subgroup.mem_bot] at hx
  rw [hx, mul_one] at he
  exact he ▸ ht

private theorem empty_levi : G.leviPoints ∅ = G.torusPoints := by
  apply le_antisymm _ (G.torus_le_leviPoints ∅)
  have hgen : G.leviPoints ∅ ⊔ G.borelPoints = G.borelPoints := by
    simpa only [Set.image_empty, Subgroup.closure_empty, sup_bot_eq] using
      levi_sup_borel_eq G ∅
  have hLB : G.leviPoints ∅ ≤ G.borelPoints := hgen ▸ le_sup_left
  intro g hg
  exact (empty_borel G) ▸ (show g ∈ G.leviBorelPoints ∅ from ⟨hg, hLB hg⟩)

private theorem borel_image :
    Set.range (Variety.mapPoints (torusInclusion G)) =
      Set.range (Variety.mapPoints (leviBorelInclusion G ∅)) := by
  ext p
  obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective p
  constructor
  · rintro ⟨t, ht⟩
    have hg : g ∈ G.torusPoints := by
      have he := (reductivePointsMulEquiv G).injective
        ((torusInclusion_points G t).symm.trans ht)
      exact he ▸ (torusPointsMulEquiv G t).property
    let b : G.leviBorelPoints ∅ := ⟨g, (empty_borel G).symm ▸ hg⟩
    refine ⟨(leviBorelPointsMulEquiv G ∅).symm b, ?_⟩
    rw [leviBorelInclusion_points, MulEquiv.apply_symm_apply]
  · rintro ⟨b, hb⟩
    have hg : g ∈ G.leviBorelPoints ∅ := by
      have he := (reductivePointsMulEquiv G).injective
        ((leviBorelInclusion_points G ∅ b).symm.trans hb)
      exact he ▸ (leviBorelPointsMulEquiv G ∅ b).property
    let t : G.torusPoints := ⟨g, (empty_borel G) ▸ hg⟩
    refine ⟨(torusPointsMulEquiv G).symm t, ?_⟩
    rw [torusInclusion_points, MulEquiv.apply_symm_apply]
    rfl

private theorem levi_image :
    Set.range (Variety.mapPoints (torusInclusion G)) =
      Set.range (Variety.mapPoints (leviInclusion G ∅)) := by
  ext p
  obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective p
  constructor
  · rintro ⟨t, ht⟩
    have hg : g ∈ G.torusPoints := by
      have he := (reductivePointsMulEquiv G).injective
        ((torusInclusion_points G t).symm.trans ht)
      exact he ▸ (torusPointsMulEquiv G t).property
    let l : G.leviPoints ∅ := ⟨g, (empty_levi G).symm ▸ hg⟩
    refine ⟨(leviPointsMulEquiv G ∅).symm l, ?_⟩
    rw [leviInclusion_points, MulEquiv.apply_symm_apply]
  · rintro ⟨l, hl⟩
    have hg : g ∈ G.leviPoints ∅ := by
      have he := (reductivePointsMulEquiv G).injective
        ((leviInclusion_points G ∅ l).symm.trans hl)
      exact he ▸ (leviPointsMulEquiv G ∅ l).property
    let t : G.torusPoints := ⟨g, (empty_levi G) ▸ hg⟩
    refine ⟨(torusPointsMulEquiv G).symm t, ?_⟩
    rw [torusInclusion_points, MulEquiv.apply_symm_apply]
    rfl

/-- The Levi subgroup and its Borel for an empty set of simple roots are the chosen torus. -/
theorem emptyLevi_isTorus :
  G.leviPoints (∅ : Set G.rootBase.support) = G.torusPoints ∧
  G.leviBorelPoints (∅ : Set G.rootBase.support) = G.torusPoints ∧
  IsIso (torusLeviBorelInclusion G (∅ : Set G.rootBase.support)) ∧
  IsIso (torusLeviBorelInclusion G (∅ : Set G.rootBase.support) ≫
    leviBorelLeviInclusion G (∅ : Set G.rootBase.support)) := by
  refine ⟨empty_levi G, empty_borel G, ?_, ?_⟩
  · exact iso_of_image (torusLeviBorelInclusion G ∅) (leviBorelInclusion G ∅)
      (torusInclusion G) (torusLeviBorelInclusion_comp G ∅) (borel_image G)
  · apply iso_of_image _ (leviInclusion G ∅) (torusInclusion G) _ (levi_image G)
    rw [Category.assoc, leviBorelLeviInclusion_comp, torusLeviBorelInclusion_comp]

end SchubertGeometry
