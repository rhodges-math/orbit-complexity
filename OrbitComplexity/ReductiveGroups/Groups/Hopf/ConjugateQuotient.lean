import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinate quotients of conjugate closed subgroups

Coordinate conjugation induces a Hopf algebra equivalence between the quotient
for a conjugated subgroup and the original quotient. Its rational points are
the corresponding conjugated point subgroup.
-/

noncomputable section
namespace ReductiveGroups
open TauCeti
variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Conjugation identifies the coordinate quotient of a conjugate subgroup with the original. -/
private def conjugateQuotientAlgEquiv (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K)) :
    (B ⧸ (I.conjugate g).toIdeal) ≃ₐ[K] (B ⧸ I.toIdeal) :=
  Ideal.quotientEquivAlg (I.conjugate g).toIdeal I.toIdeal
    (HopfAlgebra.pointConjugationBialgEquiv g).toAlgEquiv (by
      have h : (I.conjugate g).toIdeal =
          I.toIdeal.comap (HopfAlgebra.pointConjugationAlgHom g).toRingHom := by
        ext b
        change b ∈ I.conjugate g ↔ HopfAlgebra.pointConjugationAlgHom g b ∈ I
        exact HopfIdeal.mem_conjugate
      rw [h]
      exact (Ideal.map_comap_of_surjective (HopfAlgebra.pointConjugationAlgHom g).toRingHom
        (HopfAlgebra.pointConjugationBialgEquiv g).surjective I.toIdeal).symm)

private def conjugateQuotientMap (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K)) :
    (B ⧸ (I.conjugate g).toIdeal) →ₐc[K] (B ⧸ I.toIdeal) :=
  Bialgebra.Quotient.liftBialgHom (I.conjugate g).toIdeal
    ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom) (by
        intro b hb
        change Ideal.Quotient.mk I.toIdeal (HopfAlgebra.pointConjugationAlgHom g b) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_conjugate.mp hb))

/-- Conjugation identifies the Hopf coordinate algebras of a subgroup and its conjugate. -/
def conjugateQuotientEquiv (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K)) :
    (B ⧸ (I.conjugate g).toIdeal) ≃ₐc[K] (B ⧸ I.toIdeal) :=
  BialgEquiv.ofBijective (conjugateQuotientMap I g) (by
    have h : (conjugateQuotientMap I g : _ → _) = conjugateQuotientAlgEquiv I g := by
      funext a
      refine Quotient.inductionOn' a ?_
      intro b
      rfl
    rw [h]
    exact (conjugateQuotientAlgEquiv I g).bijective)

/-- On coordinate classes the conjugate quotient map is coordinate conjugation. -/
theorem conjugateQuotientEquiv_mk (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K)) (b : B) :
    conjugateQuotientEquiv I g (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk I.toIdeal (HopfAlgebra.pointConjugationAlgHom g b) := rfl

/-- Rational points of a conjugate quotient are the conjugated subgroup of rational points. -/
theorem conjugatePoints_eq (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K)) :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) (I.conjugate g)
        (CommAlgCat.of K K) =
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K)).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · apply (CommHopfAlgCat.pointConjugation_mem_conjugate_iff I g
        (CommAlgCat.of K K) (g⁻¹ * x * g)).mp
      simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
        AlgHom.mapValue_id, MonoidHom.id_apply, mul_assoc, mul_inv_cancel_left,
        mul_inv_cancel, mul_one] using hx
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    have h := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff I g
      (CommAlgCat.of K K) v).mpr hv
    change g * v * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) (I.conjugate g) (CommAlgCat.of K K)
    simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
      AlgHom.mapValue_id, MonoidHom.id_apply] using h

end ReductiveGroups
