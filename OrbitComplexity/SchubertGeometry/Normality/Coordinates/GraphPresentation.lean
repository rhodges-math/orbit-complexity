import Batteries.Tactic.Lint
import OrbitComplexity.GroupActions.Rosenlicht.GraphPresentation
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.EliminationInclusion

/-! # Finite polynomial graph presentations of algebra inclusions

The second variable block presents the original source algebra. Its ideal is
the contraction of the target relation ideal, and the induced quotient map
recovers the original algebra homomorphism.
-/

open MvPolynomial

open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

/-- An injective map of finite-type algebras is the retained-variable
map between finite polynomial quotients, with the source ideal given by
contraction of the target ideal. No domain or reducedness hypothesis is needed. -/
theorem exists_injective_graph_presentation {K A B : Type*}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (f : A →ₐ[K] B) (hf : Function.Injective f) :
    ∃ m n : ℕ, ∃ J : Ideal (MvPolynomial (Fin n ⊕ₗ Fin m) K),
      ∃ eA : (MvPolynomial (Fin m) K ⧸
        J.comap (rename (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m)).toRingHom) ≃ₐ[K] A,
      ∃ eB : (MvPolynomial (Fin n ⊕ₗ Fin m) K ⧸ J) ≃ₐ[K] B,
        eB.toAlgHom.comp (eliminationQuotientMap J) = f.comp eA.toAlgHom := by
  classical
  obtain ⟨m, source, hsource⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := K) (S := A)).mp inferInstance
  obtain ⟨n, J, eB, hB⟩ := GroupActions.exists_graph_presentation K B m (f.comp source)
  let retained : MvPolynomial (Fin m) K →ₐ[K]
      (MvPolynomial (Fin n ⊕ₗ Fin m) K ⧸ J) :=
    (Ideal.Quotient.mkₐ K J).comp (rename Sum.inrₗ)
  have hretained : eB.toAlgHom.comp retained = f.comp source := by
    calc
      eB.toAlgHom.comp retained = eB.toAlgHom.comp
          ((GroupActions.quotientVariableMap J
            (Set.range (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m))).comp
              (rename (GroupActions.rightVariableEquiv n m))) := by
        congr 1
        ext i
        simp only [retained, AlgHom.comp_apply, rename_X,
          GroupActions.quotientVariableMap_X, GroupActions.rightVariableEquiv_val,
          Ideal.Quotient.mkₐ_eq_mk]
      _ = f.comp source := hB
  have hrelation :
      J.comap (rename (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m)).toRingHom =
        RingHom.ker source := by
    ext p
    change rename (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m) p ∈ J ↔ source p = 0
    have hp : eB (retained p) = f (source p) := AlgHom.congr_fun hretained p
    constructor
    · intro h
      have hz : retained p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
      apply hf
      calc
        f (source p) = eB (retained p) := hp.symm
        _ = 0 := by rw [hz, map_zero]
        _ = f 0 := (map_zero f).symm
    · intro h
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply eB.injective
      change eB (retained p) = eB 0
      rw [hp, h, map_zero, map_zero]
  let eA := (Ideal.quotientEquivAlgOfEq K hrelation).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsource)
  refine ⟨m, n, J, eA, eB, ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change eB (Ideal.Quotient.mk J (rename Sum.inrₗ p)) =
    f (eA (Ideal.Quotient.mk _ p))
  have heA : eA (Ideal.Quotient.mk _ p) = source p := by
    change Ideal.quotientKerAlgEquivOfSurjective hsource
      (Ideal.quotientEquivAlgOfEq K hrelation (Ideal.Quotient.mk _ p)) = source p
    rw [Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
  rw [heA]
  exact AlgHom.congr_fun hretained p

end
end SchubertGeometry
