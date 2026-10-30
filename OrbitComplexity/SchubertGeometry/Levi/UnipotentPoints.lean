import OrbitComplexity.SchubertGeometry.Levi.Connected
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviOpposite
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple

/-!
# Unipotent subgroups inside Levi Borels

A normal subgroup contained in a Levi Borel lies in the intersection with its
parabolic-longest conjugate, hence in the torus. Its points are both semisimple
and unipotent and therefore are the identity. Reduced point separation
identifies its defining ideal with the augmentation ideal.
-/

noncomputable section
namespace SchubertGeometry
open TauCeti ReductiveGroups CategoryTheory WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def leviQuotient (I : Set G.rootBase.support) :
    (CommHopfAlgCat.of K G.coordinateAlgebra) ⟶ (G.leviAlgebra I).obj :=
  CommHopfAlgCat.mkQuotient _ (G.leviIdeal I)

private theorem leviQuotient_surjective (I : Set G.rootBase.support) :
    Function.Surjective (leviQuotient G I).hom := CommHopfAlgCat.mkQuotient_surjective _ _

private theorem leviBorel_mem_ideal (I : Set G.rootBase.support)
    (a : G.coordinateAlgebra) (ha : a ∈ G.leviBorelIdeal I) :
    (leviQuotient G I).hom a ∈ leviBorelIdealInLevi G I := by
  unfold leviBorelIdealInLevi
  rw [HopfIdeal.mem_kerOfSurjective]
  change (CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.leviIdeal_le_leviBorel I)).hom
        (Ideal.Quotient.mkₐ K (G.leviIdeal I).toIdeal a) = 0
  rw [CommHopfAlgCat.quotientMapOfLe_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

private theorem leviNormal_points_torus (I : Set G.rootBase.support)
    (J : HopfIdeal K (G.leviAlgebra I))
    (hnormal : J.IsNormal) (hBJ : leviBorelIdealInLevi G I ≤ J) :
    (CommHopfAlgCat.quotientPointsSubgroup (G.leviAlgebra I).obj J (CommAlgCat.of K K)).map
      (AlgHom.mapDomain (leviQuotient G I).hom) ≤ G.torusPoints := by
  let p := AlgHom.mapDomain (leviQuotient G I).hom (A := K)
  let N₀ := CommHopfAlgCat.quotientPointsSubgroup (G.leviAlgebra I).obj J (CommAlgCat.of K K)
  have hN : N₀.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal _ J hnormal _
  let : N₀.Normal := hN
  apply G.leviNormalPoints_le_torus I (N₀.map p)
  · rintro b ⟨x, hx, rfl⟩
    rw [← G.leviBorelIdeal_points I]
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
    intro a ha
    change x.ofConv ((leviQuotient G I).hom a) = 0
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hx _
      (hBJ (leviBorel_mem_ideal G I a ha))
  · have hr : p.range = G.leviPoints I := G.leviIdeal_points I
    rw [← hr]
    have h := N₀.le_normalizer_map p
    simpa only [Subgroup.normalizer_eq_top, Subgroup.map_top] using h

/-- A normal smooth unipotent Levi subgroup contained in its Borel is trivial. -/
theorem levi_unipotent_eq_of_le (I : Set G.rootBase.support)
    (J : HopfIdeal K (G.leviAlgebra I)) (hnormal : J.IsNormal)
    (hBJ : leviBorelIdealInLevi G I ≤ J)
    (hU : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) J)) :
    J = HopfIdeal.augmentation K (G.leviAlgebra I) := by
  let H := G.leviAlgebra I
  let Q := FiniteTypeCommHopfAlgCat.quotient H J
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff K Q).mp hU
  let : Algebra.Smooth K Q := hU'.1
  let : IsReduced Q := isReduced_of_smooth K Q
  have hT := leviNormal_points_torus G I J hnormal hBJ
  let qJ : H →ₐc[K] Q := (CommHopfAlgCat.mkQuotient H.obj J).hom
  let qL := (leviQuotient G I).hom
  have hgOne (g : WithConv (Q →ₐ[K] K)) : g = 1 := by
    let x := AlgHom.mapDomain qJ g
    have hx : x ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of K K) :=
      ⟨g, rfl⟩
    have hpT : AlgHom.mapDomain qL x ∈ G.torusPoints :=
      hT (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    obtain ⟨t, ht⟩ := (ReductiveGroups.mem_torusPoints_iff G.torusIdeal G.torusSplit
      G.split_surjective G.split_eq_zero _).mp hpT
    have hsem : HopfAlgebra.IsSemisimplePoint (AlgHom.mapDomain qL x) := by
      rw [ht]
      exact (DiagonalizableGroup.isSemisimplePoint t).mapDomain G.torusSplit
    have hunip : HopfAlgebra.IsUnipotentPoint (AlgHom.mapDomain qL x) :=
      ((smoothUnipotentCommHopfAlgProperty.isUnipotentPoint hU g).mapDomain qJ).mapDomain qL
    have he := hsem.eq_one_of_isUnipotent hunip
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    obtain ⟨b, rfl⟩ := CommHopfAlgCat.mkQuotient_surjective H.obj J a
    obtain ⟨c, rfl⟩ := leviQuotient_surjective G I b
    have hv : g.ofConv (qJ (qL c)) = (1 : G.points).ofConv c :=
      congrArg (fun z : G.points => z.ofConv c) he
    simpa only [AlgHom.convOne_apply,
      CoalgHomClass.counit_comp_apply, Algebra.algebraMap_self, RingHom.id_apply] using hv
  apply HopfIdeal.ext
  intro a
  rw [HopfIdeal.mem_augmentation]
  constructor
  · exact J.counit_eq_zero
  · intro ha
    apply (CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj J a).mp
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
    intro f
    have h := congrArg (fun g : WithConv (Q →ₐ[K] K) => g.ofConv (qJ a)) (hgOne (toConv f))
    simpa only [AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply, ha,
      map_zero, Algebra.algebraMap_self, RingHom.id_apply] using h

end SchubertGeometry
