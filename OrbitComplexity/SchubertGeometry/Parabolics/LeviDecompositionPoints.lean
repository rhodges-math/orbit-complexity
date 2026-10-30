import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupParabolicNormalizer
import OrbitComplexity.SchubertGeometry.Levi.Center
import OrbitComplexity.SchubertGeometry.Parabolics.Subgroup

/-! # Levi factorization on parabolic points

The outside-subsystem positive-root group is normal in the standard parabolic.
Its intersection with the Levi is trivial, and every parabolic point has unique Levi factors.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions TauCeti
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The positive-root point subgroup outside the chosen Levi subsystem. -/
def parabolicUnipotentPoints (I : Set G.rootBase.support) : Subgroup G.points :=
  G.rootSubsetPoints (parabolicRadicalRoots G.rootBase I)
    (parabolicRadicalRoots_closed G.rootBase I)

private theorem unipotent_le_borel (I : Set G.rootBase.support) :
    parabolicUnipotentPoints G I ≤ G.borelPoints :=
  (G.rootSubsetPoints_le_unipotent _ _).trans G.unipotent_le_borel

/-- The standard parabolic normalizes its outside-subsystem positive-root subgroup. -/
theorem parabolicUnipotent_normalizer (I : Set G.rootBase.support) :
    standardParabolicPoints G I ≤
      Subgroup.normalizer (parabolicUnipotentPoints G I : Set G.points) := by
  let H := Subgroup.normalizer (parabolicUnipotentPoints G I : Set G.points)
  apply sup_le (G.borel_le_parabolicNormalizer I)
  apply (Subgroup.closure_le H).mpr
  rintro _ ⟨i, hi, rfl⟩
  let w := simpleWeylWord G.rootBase [i]
  have hw : w ∈ standardParabolicSubgroup G.rootBase I := by
    apply SimpleWeylWord.mem_standardParabolicSubgroup G.rootBase I [i]
    intro j hj
    have he : j = i := List.mem_singleton.mp hj
    exact he.symm ▸ hi
  obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.simple_eq_mul_weylElementPoint G.rootBase i
  have he' : G.reflectionPoint i.val = t * G.weylPoint w := by
    simpa only [w, simpleWeylWord, mul_one, G.weylPoint_eq] using he
  change G.reflectionPoint i.val ∈ H
  rw [he']
  exact H.mul_mem (G.torusPoints_le_rootNormalizer _ _ ht)
    (G.weyl_mem_parabolicNormalizer I w hw)

/-- The outside-subsystem positive-root group is normal in the parabolic point group. -/
instance parabolicUnipotent_normal (I : Set G.rootBase.support) :
    ((parabolicUnipotentPoints G I).subgroupOf (standardParabolicPoints G I)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (parabolicUnipotent_normalizer G I)

private theorem borel_le_levi_unipotent (I : Set G.rootBase.support) :
    G.borelPoints ≤ G.leviPoints I ⊔ parabolicUnipotentPoints G I := by
  let H := G.leviPoints I ⊔ parabolicUnipotentPoints G I
  intro b hb
  obtain ⟨t, ht, u, hu, htu⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive b hb
  have hufull : u ∈ G.rootSubsetPoints {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) := by
    rw [G.fullRootPoints_eq_unipotent]
    exact hu
  have hp := parabolicRadicalRoots_partition G.rootBase I
  obtain ⟨p, ⟨hl, hr, he⟩, _⟩ := G.rootSubsetPoints_existsUnique_mul _ _ _
    (isPositiveRootClosed_isPos G.rootBase) (LeviRootSpan.isPositiveRootClosed G.rootBase I)
    (parabolicRadicalRoots_closed G.rootBase I) hp.1 hp.2 u hufull
  have hlL := G.rootSubsetPoints_le_leviPoints I _
    (LeviRootSpan.isPositiveRootClosed G.rootBase I) (fun _ h => h) hl
  rw [← htu, ← he]
  have hleft : G.leviPoints I ≤ H := le_sup_left
  have hright : parabolicUnipotentPoints G I ≤ H := le_sup_right
  exact H.mul_mem (hleft (G.torus_le_leviPoints I ht))
    (H.mul_mem (hleft hlL) (hright hr))

/-- The Levi and outside-subsystem positive-root groups generate the standard parabolic. -/
theorem parabolic_eq_levi_sup_unipotent (I : Set G.rootBase.support) :
    standardParabolicPoints G I = G.leviPoints I ⊔ parabolicUnipotentPoints G I := by
  change G.borelPoints ⊔ Subgroup.closure _ = _
  rw [← levi_sup_borel_eq G I]
  apply le_antisymm
  · exact sup_le le_sup_left (borel_le_levi_unipotent G I)
  · exact sup_le le_sup_left ((unipotent_le_borel G I).trans le_sup_right)

/-- The Levi meets the outside-subsystem positive-root group only in the identity. -/
theorem levi_disjoint_parabolicUnipotent (I : Set G.rootBase.support) :
    Disjoint (G.leviPoints I) (parabolicUnipotentPoints G I) := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro g hg
  have hUL : g ∈ G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
    rw [← G.levi_unipotent_eq I]
    exact ⟨hg.1, G.rootSubsetPoints_le_unipotent _ _ hg.2⟩
  have hfull : g ∈ G.rootSubsetPoints {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) := by
    rw [G.fullRootPoints_eq_unipotent]
    exact G.rootSubsetPoints_le_unipotent _ _ hg.2
  have hp := parabolicRadicalRoots_partition G.rootBase I
  obtain ⟨p, _, huniq⟩ := G.rootSubsetPoints_existsUnique_mul _ _ _
    (isPositiveRootClosed_isPos G.rootBase) (LeviRootSpan.isPositiveRootClosed G.rootBase I)
    (parabolicRadicalRoots_closed G.rootBase I) hp.1 hp.2 g hfull
  have hleft := huniq (g, 1) ⟨hUL, (parabolicUnipotentPoints G I).one_mem, mul_one g⟩
  have hright := huniq (1, g)
    ⟨(G.rootSubsetPoints _ (LeviRootSpan.isPositiveRootClosed G.rootBase I)).one_mem,
      hg.2, one_mul g⟩
  exact congrArg Prod.fst (hleft.trans hright.symm)

/-- Every parabolic point has unique Levi and outside-subsystem positive-root factors. -/
theorem parabolic_existsUnique_levi_mul (I : Set G.rootBase.support)
    (g : G.points) (hg : g ∈ standardParabolicPoints G I) :
    ∃! p : G.points × G.points,
      p.1 ∈ G.leviPoints I ∧ p.2 ∈ parabolicUnipotentPoints G I ∧ p.1 * p.2 = g := by
  have hLP : G.leviPoints I ≤ standardParabolicPoints G I := by
    rw [parabolic_eq_levi_sup_unipotent]
    exact le_sup_left
  have hLN := hLP.trans (parabolicUnipotent_normalizer G I)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right
    (G.leviPoints I) (parabolicUnipotentPoints G I) hLN
  have hg' : g ∈ (G.leviPoints I ⊔ parabolicUnipotentPoints G I : Subgroup G.points) :=
    parabolic_eq_levi_sup_unipotent G I ▸ hg
  change g ∈ ((G.leviPoints I ⊔ parabolicUnipotentPoints G I :
    Subgroup G.points) : Set G.points) at hg'
  rw [hset] at hg'
  obtain ⟨l, hl, u, hu, he⟩ := hg'
  refine ⟨(l, u), ⟨hl, hu, he⟩, ?_⟩
  rintro ⟨l', u'⟩ ⟨hl', hu', he'⟩
  have hrel : l⁻¹ * l' = u * u'⁻¹ := by
    calc
      l⁻¹ * l' = l⁻¹ * (l' * u') * u'⁻¹ := by group
      _ = l⁻¹ * (l * u) * u'⁻¹ := by rw [he', ← he]
      _ = u * u'⁻¹ := by group
  have hboth : l⁻¹ * l' ∈ G.leviPoints I ⊓ parabolicUnipotentPoints G I :=
    ⟨(G.leviPoints I).mul_mem ((G.leviPoints I).inv_mem hl) hl',
      hrel ▸ (parabolicUnipotentPoints G I).mul_mem hu
        ((parabolicUnipotentPoints G I).inv_mem hu')⟩
  have hbot := disjoint_iff.mp (levi_disjoint_parabolicUnipotent G I)
  have hid : l⁻¹ * l' = 1 := by
    simpa only [hbot, Subgroup.mem_bot] using hboth
  have hlEq : l' = l := (inv_mul_eq_one.mp hid).symm
  have huEq : u' = u := by
    rw [hlEq] at he'
    exact mul_left_cancel (he'.trans he.symm)
  exact Prod.ext hlEq huEq

end SchubertGeometry
