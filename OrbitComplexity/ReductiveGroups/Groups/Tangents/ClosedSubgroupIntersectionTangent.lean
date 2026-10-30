import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# Closed Subgroup Intersection Tangent

The tangent of a scheme-theoretic intersection of closed affine
subgroups is the intersection of their tangent images. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Tangent membership for the original quotient by a Hopf ideal. -/
theorem tangent_mem_hopfQuotient_iff
    (I : TauCeti.HopfIdeal K B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range ↔
      ∀ b ∈ I, d b = 0 := by
  rw [tangent_mem_range_iff_kills_kernel _
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective (CommHopfAlgCat.of K B) I)]
  have hq (b : B) :
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom b = 0 ↔
        b ∈ I :=
    TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff (CommHopfAlgCat.of K B) I b
  simp only [hq]

/-- Ideal sum is the scheme-theoretic subgroup intersection, and
its quotient differential has exactly the intersection tangent image. -/
theorem hopfQuotient_sup_tangentImage
    (I J : TauCeti.HopfIdeal K B) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) (I ⊔ J)).hom).range =
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range ⊓
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  ext d
  change (d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) (I ⊔ J)).hom).range) ↔
    (d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range ∧
     d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range)
  rw [tangent_mem_hopfQuotient_iff (K := K) (B := B) (I ⊔ J) d,
    tangent_mem_hopfQuotient_iff (K := K) (B := B) I d,
    tangent_mem_hopfQuotient_iff (K := K) (B := B) J d]
  constructor
  · intro h
    exact ⟨fun b hb => h b (Ideal.mem_sup_left hb),
      fun b hb => h b (Ideal.mem_sup_right hb)⟩
  · rintro ⟨hI, hJ⟩ b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := TauCeti.HopfIdeal.mem_sup.mp hb
    rw [map_add, hI a ha, hJ c hc, add_zero]

end ReductiveGroups
