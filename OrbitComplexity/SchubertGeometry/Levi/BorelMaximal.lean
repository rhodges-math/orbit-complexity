import OrbitComplexity.SchubertGeometry.Levi.Connected
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ConnectedSubgroupTangentEquality
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SolvableTangent

/-!
# Maximality of Levi Borel subgroups

A smooth connected solvable subgroup containing the Levi Borel has the
same tangent space. The smooth connected subgroup tangent criterion then
identifies their defining Hopf ideals.
-/

noncomputable section
namespace SchubertGeometry
open TauCeti ReductiveGroups CategoryTheory WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem candidate_points_solvable (J : HopfIdeal K G.coordinateAlgebra)
    (hJ : HopfIdeal.IsBorelCandidate K (FiniteTypeCommHopfAlgCat.of K G.coordinateAlgebra) J) :
    Group.IsSolvable (WithConv ((G.coordinateAlgebra ⧸ J.toIdeal) →ₐ[K] K)) := by
  let Q := CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra) J
  let : Group.IsSolvable (WithConv (Q →ₐ[K] AlgebraicClosure K)) := hJ.geometricallySolvable
  let f : K →ₐ[K] AlgebraicClosure K := Algebra.ofId K (AlgebraicClosure K)
  exact Group.isSolvable_of_isSolvable_injective
    (f := AlgHom.mapValue (H := Q) f) (AlgHom.mapValue_injective (algebraMap K _).injective)

private theorem ambientCandidate_eq (I : Set G.rootBase.support)
    (J : HopfIdeal K G.coordinateAlgebra)
    (hJ : HopfIdeal.IsBorelCandidate K (FiniteTypeCommHopfAlgCat.of K G.coordinateAlgebra) J)
    (hLJ : G.leviIdeal I ≤ J) (hJB : J ≤ G.leviBorelIdeal I) :
    J = G.leviBorelIdeal I := by
  let : Algebra.Smooth K (G.coordinateAlgebra ⧸ J.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp hJ.smooth
  let : IsReduced (G.coordinateAlgebra ⧸ J.toIdeal) := isReduced_of_smooth K _
  let : Group.IsSolvable (WithConv ((G.coordinateAlgebra ⧸ J.toIdeal) →ₐ[K] K)) :=
    candidate_points_solvable G J hJ
  let : LieAlgebra.IsSolvable
      (Derivation K (G.coordinateAlgebra ⧸ J.toIdeal)
        (Bialgebra.CounitAlgebra K (G.coordinateAlgebra ⧸ J.toIdeal) K)) :=
    SolvableTangent.isSolvable_of_rational_points_isSolvable
  let : LieAlgebra.IsSolvable (G.subgroupTangent J) := by
    change LieAlgebra.IsSolvable
      (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra) J).hom).range
    infer_instance
  have ht := G.leviBorelTangent_maximal I (G.subgroupTangent J)
    (hopfQuotient_tangentImage_antitone _ _ hJB)
    (hopfQuotient_tangentImage_antitone _ _ hLJ)
  apply HopfIdeals.eq_of_le_of_smooth_connected_tangent J (G.leviBorelIdeal I) hJB
    hJ.smooth
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace K _).mp
      hJ.geometricallyConnected)
    ((smoothCommHopfAlgProperty_iff _).mpr (G.leviBorel_smooth I))
  · change ConnectedSpace (leviBorelVariety G I).scheme
    infer_instance
  · exact ht.le

private def leviQuotient (I : Set G.rootBase.support) :
    (CommHopfAlgCat.of K G.coordinateAlgebra) ⟶ (G.leviAlgebra I).obj :=
  CommHopfAlgCat.mkQuotient _ (G.leviIdeal I)

private theorem leviQuotient_surjective (I : Set G.rootBase.support) :
    Function.Surjective (leviQuotient G I).hom := CommHopfAlgCat.mkQuotient_surjective _ _

private theorem leviBorel_comap (I : Set G.rootBase.support) :
    (leviBorelIdealInLevi G I).comapOfSurjective
      (leviQuotient G I).hom (leviQuotient_surjective G I) = G.leviBorelIdeal I := by
  ext a
  rw [HopfIdeal.mem_comapOfSurjective]
  unfold leviBorelIdealInLevi
  rw [HopfIdeal.mem_kerOfSurjective]
  change (CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.leviIdeal_le_leviBorel I)).hom
        (Ideal.Quotient.mkₐ K (G.leviIdeal I).toIdeal a) = 0 ↔ a ∈ G.leviBorelIdeal I
  rw [CommHopfAlgCat.quotientMapOfLe_mk]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The Levi Borel subgroup is maximal among smooth connected solvable subgroups over the field. -/
theorem leviBorel_isBorelOverAlgClosed (I : Set G.rootBase.support) :
    HopfIdeal.IsBorelOverAlgClosed K (G.leviAlgebra I) (leviBorelIdealInLevi G I) := by
  refine ⟨inferInstance, leviBorel_candidate G I, ?_⟩
  intro J hJ hJB
  let q := leviQuotient G I
  have hq : Function.Surjective q.hom := leviQuotient_surjective G I
  let J' := J.comapOfSurjective q.hom hq
  let e := CommHopfAlgCat.quotientIsoOfSurjective q hq J
  have hJ' : HopfIdeal.IsBorelCandidate K
      (FiniteTypeCommHopfAlgCat.of K G.coordinateAlgebra) J' := by
    apply HopfIdeal.IsBorelCandidate.mk
    · exact (smoothCommHopfAlgProperty K).prop_of_iso e.symm hJ.smooth
    · exact (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso e.symm
        hJ.geometricallyConnected
    · exact (geometricallySolvablePointsCommHopfAlgProperty K).prop_of_iso e.symm
        hJ.geometricallySolvable
  have hLJ : G.leviIdeal I ≤ J' := by
    intro a ha
    apply HopfIdeal.mem_comapOfSurjective.mpr
    have hz : q.hom a = 0 := (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr ha
    exact hz ▸ J.toIdeal.zero_mem
  have hJ'B : J' ≤ G.leviBorelIdeal I := by
    rw [← leviBorel_comap G I]
    exact (HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff q.hom hq).mpr hJB
  have heq : J' = G.leviBorelIdeal I := ambientCandidate_eq G I J' hJ' hLJ hJ'B
  apply (HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff q.hom hq).mp
  exact (leviBorel_comap G I).trans heq.symm |>.le

end SchubertGeometry
