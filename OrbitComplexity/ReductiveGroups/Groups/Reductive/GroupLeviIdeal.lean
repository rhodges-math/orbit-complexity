import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviPoints
import OrbitComplexity.ReductiveGroups.Groups.Hopf.HopfAutomorphismFixedSubgroup
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing

/-!
# Reduced standard Levi coordinate algebras

Fixed-point Hopf ideals show that the Levi point centralizer is closed.
Vanishing ideals give reduced coordinate quotients for it and its Borel intersection.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem point_conjugation (z x : G.points) :
    x.ofConv.comp (HopfAlgebra.pointConjugationBialgEquiv z).toAlgEquiv.toAlgHom =
      (z * x * z⁻¹).ofConv := by
  change x.ofConv.comp ((HopfAlgebra.pointConjugationBialgEquiv z :
    G.coordinateAlgebra →ₐc[K] G.coordinateAlgebra) :
      G.coordinateAlgebra →ₐ[K] G.coordinateAlgebra) = (z * x * z⁻¹).ofConv
  rw [HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  have h := congrArg WithConv.ofConv (HopfAlgebra.comp_pointConjugationAlgHom z x)
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl, AlgHom.mapValue_id,
    MonoidHom.id_apply, WithConv.ofConv_toConv] using h

private def leviFixedIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  hopfAutomorphismFixedHopfIdeal
    (fun z : G.leviCenterPoints I => HopfAlgebra.pointConjugationBialgEquiv z.val)

private theorem leviFixedIdeal_points (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.leviFixedIdeal I) (CommAlgCat.of K K) = G.leviPoints I := by
  ext x
  rw [leviFixedIdeal, mem_hopfAutomorphismFixed_iff]
  constructor
  · intro h
    change ∀ z ∈ G.leviCenterPoints I, z * x = x * z
    intro z hz
    have he := h ⟨z, hz⟩
    rw [G.point_conjugation] at he
    exact (mul_inv_eq_iff_eq_mul).mp (WithConv.ofConv_injective he)
  · intro hx z
    change x.ofConv.comp
      (HopfAlgebra.pointConjugationBialgEquiv z.val).toAlgEquiv.toAlgHom = x.ofConv
    rw [G.point_conjugation]
    apply congrArg WithConv.ofConv
    apply (mul_inv_eq_iff_eq_mul).mpr
    exact hx z.val z.property

/-- The reduced closed subgroup ideal of the standard Levi point group. -/
def leviIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (G.leviPoints I)

/-- The affine coordinate Hopf algebra of the standard Levi subgroup. -/
def leviAlgebra (I : Set G.rootBase.support) : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra (G.leviIdeal I)

/-- The reduced Levi coordinate quotient has exactly the standard Levi points. -/
theorem leviIdeal_points (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.leviIdeal I) (CommAlgCat.of K K) = G.leviPoints I := by
  have hfixed : G.leviFixedIdeal I ≤ G.leviIdeal I := by
    apply (HopfIdeal.le_vanishingIdeal_iff (G.leviPoints I) (G.leviFixedIdeal I)).mpr
    rw [G.leviFixedIdeal_points]
  apply le_antisymm
  · have h := CommHopfAlgCat.quotientPointsSubgroup_le_of_le
      (CommHopfAlgCat.of K G.coordinateAlgebra) hfixed (CommAlgCat.of K K)
    rw [G.leviFixedIdeal_points] at h
    exact h
  · exact (HopfIdeal.le_vanishingIdeal_iff (G.leviPoints I) (G.leviIdeal I)).mp le_rfl

/-- The Levi coordinate algebra is reduced. -/
instance leviAlgebra_isReduced (I : Set G.rootBase.support) : IsReduced (G.leviAlgebra I) := by
  change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
    (HopfIdeal.vanishingIdeal (G.leviPoints I)))
  infer_instance

/-- The reduced closed subgroup ideal of the Levi--Borel intersection. -/
def leviBorelIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (G.leviBorelPoints I)

/-- The coordinate Hopf algebra of the Levi--Borel subgroup. -/
def leviBorelAlgebra (I : Set G.rootBase.support) : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra (G.leviBorelIdeal I)

/-- The reduced Levi--Borel coordinate quotient has exactly the Levi--Borel points. -/
theorem leviBorelIdeal_points (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.leviBorelIdeal I) (CommAlgCat.of K K) = G.leviBorelPoints I := by
  have hlevi : G.leviIdeal I ≤ G.leviBorelIdeal I := by
    apply (HopfIdeal.le_vanishingIdeal_iff (G.leviBorelPoints I) (G.leviIdeal I)).mpr
    rw [G.leviIdeal_points]
    exact inf_le_left
  have hborel : G.borelIdeal ≤ G.leviBorelIdeal I :=
    (HopfIdeal.le_vanishingIdeal_iff (G.leviBorelPoints I) G.borelIdeal).mpr inf_le_right
  apply le_antisymm
  · intro b hb
    exact ⟨by
      rw [← G.leviIdeal_points]
      exact CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hlevi _ hb,
      CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hborel _ hb⟩
  · exact (HopfIdeal.le_vanishingIdeal_iff (G.leviBorelPoints I)
      (G.leviBorelIdeal I)).mp le_rfl

/-- The Levi--Borel coordinate algebra is reduced. -/
instance leviBorelAlgebra_isReduced (I : Set G.rootBase.support) :
    IsReduced (G.leviBorelAlgebra I) := by
  change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
    (HopfIdeal.vanishingIdeal (G.leviBorelPoints I)))
  infer_instance

end ReductiveGroups.ReductiveGroupData
