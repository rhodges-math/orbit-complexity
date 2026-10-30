import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Containment
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent

/-!
# Connected Subgroup Tangent Equality

A smooth connected closed subgroup with the full tangent space
equals its ambient smooth connected group. All tangent maps are the
differentials of the original coordinate quotient maps. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [HopfAlgebra K A] [HopfAlgebra K B]

/-- A closed immersion of smooth connected affine groups whose
differential is onto is an isomorphism on coordinate algebras. -/
theorem HopfMap.of_smooth_connected_tangent_surjective
    [Algebra.FiniteType K A] (f : A →ₐc[K] B)
    (hf : Function.Surjective f)
    (hA : TauCeti.smoothCommHopfAlgProperty K (CommHopfAlgCat.of K A))
    (hAc : ConnectedSpace (PrimeSpectrum A))
    (hB : TauCeti.smoothCommHopfAlgProperty K (CommHopfAlgCat.of K B))
    (hBc : ConnectedSpace (PrimeSpectrum B))
    (hdf : Function.Surjective (TauCeti.derivationCompLieHom (B := K) f)) :
    Function.Injective f := by
  apply (TauCeti.HopfIdeal.ker_eq_bot_iff f).mp
  apply TauCeti.HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot
    f hf hA hAc hB hBc
  exact
    TauCeti.HopfIdeal.conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective
    f hf hdf

/-- Nested smooth connected closed subgroups with the same tangent
image have the same defining ideal. Only the nonautomatic tangent inclusion
is needed as a premise. -/
theorem HopfIdeals.eq_of_le_of_smooth_connected_tangent
    [Algebra.FiniteType K B] (I J : TauCeti.HopfIdeal K B) (hIJ : I ≤ J)
    (hI : TauCeti.smoothCommHopfAlgProperty K
      (TauCeti.CommHopfAlgCat.quotient (CommHopfAlgCat.of K B) I))
    (hIc : ConnectedSpace (PrimeSpectrum (B ⧸ I.toIdeal)))
    (hJ : TauCeti.smoothCommHopfAlgProperty K
      (TauCeti.CommHopfAlgCat.quotient (CommHopfAlgCat.of K B) J))
    (hJc : ConnectedSpace (PrimeSpectrum (B ⧸ J.toIdeal)))
    (ht : (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range ≤
      (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range) :
    I = J := by
  let qI := (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom
  let qJ := (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom
  let f := (TauCeti.CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K B) hIJ).hom
  have hcomp : f.comp qI = qJ := by
    ext b
    exact TauCeti.CommHopfAlgCat.quotientMapOfLe_mk (CommHopfAlgCat.of K B) hIJ b
  have hdqI : Function.Injective (TauCeti.derivationCompLieHom (B := K) qI) :=
    TauCeti.derivationCompLieHom_injective_of_surjective qI
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective (CommHopfAlgCat.of K B) I)
  have hdf : Function.Surjective (TauCeti.derivationCompLieHom (B := K) f) := by
    intro d
    obtain ⟨e, he⟩ := ht (show TauCeti.derivationCompLieHom (B := K) qI d ∈
        (TauCeti.derivationCompLieHom (B := K) qI).range from ⟨d, rfl⟩)
    refine ⟨e, hdqI ?_⟩
    change ((TauCeti.derivationCompLieHom (B := K) qI).comp
      (TauCeti.derivationCompLieHom (B := K) f)) e = _
    rw [← TauCeti.derivationCompLieHom_comp, hcomp]
    exact he
  have hf : Function.Injective f :=
    HopfMap.of_smooth_connected_tangent_surjective f
      (TauCeti.CommHopfAlgCat.quotientMapOfLe_surjective (CommHopfAlgCat.of K B) hIJ)
      hI hIc hJ hJc hdf
  apply le_antisymm hIJ
  intro b hb
  apply (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff
    (CommHopfAlgCat.of K B) I b).mp
  apply hf
  rw [map_zero]
  change (f.comp qI) b = 0
  rw [hcomp]
  exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff
    (CommHopfAlgCat.of K B) J b).mpr hb

end ReductiveGroups
