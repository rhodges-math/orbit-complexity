import OrbitComplexity.GroupActions.Rosenlicht.EliminationSpread
import OrbitComplexity.GroupActions.Rosenlicht.GraphPresentation
import OrbitComplexity.GroupActions.Rosenlicht.KernelTransport

/-!
# Uniform specialization of finite-type polynomial maps

A polynomial map into a finite-type algebra is a selected-coordinate map in
a graph presentation. Uniform specialization of elimination kernels, transported
through that presentation, preserves its complete relation ideal after one
denominator is inverted.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v w

/-- For a polynomial map into a finite-type algebra over a Noetherian domain,
one nonzero base element makes its complete kernel commute with every
coefficient extension. -/
theorem exists_polynomial_kernel_baseChange
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (m : ℕ) (f : MvPolynomial (Fin m) R →ₐ[R] A) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type w) [CommRing C] [Algebra R C],
      IsUnit (algebraMap R C d) →
        RingHom.ker (polynomialTensorMap C f) =
          (RingHom.ker f).map (MvPolynomial.map (algebraMap R C)) := by
  obtain ⟨n, I, eA, hf⟩ := exists_graph_presentation R A m f
  let t := Set.range (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m)
  let eT := rightVariableEquiv n m
  let q := quotientVariableMap I t
  let rR := MvPolynomial.renameEquiv R eT
  have hf' : eA.toAlgHom.comp (q.comp rR.toAlgHom) = f := hf
  have hker : RingHom.ker f = RingHom.ker (q.comp rR.toAlgHom) := by
    rw [← hf']
    change RingHom.ker (eA.toRingHom.comp (q.comp rR.toAlgHom).toRingHom) = _
    exact RingHom.ker_comp_of_injective _ eA.injective
  obtain ⟨d, hd, heq⟩ := exists_elimination_baseChange R I t
    (rightVariables_isUpperSet n m)
  refine ⟨d, hd, ?_⟩
  intro C _ _ hunit
  have hq : RingHom.ker (polynomialTensorMap C q) =
      (RingHom.ker q).map (MvPolynomial.map (algebraMap R C)) := by
    rw [← ker_quotientVariableMap_tensor C I t]
    exact heq C hunit
  have hkerC : RingHom.ker (polynomialTensorMap C f) =
      RingHom.ker (polynomialTensorMap C (q.comp rR.toAlgHom)) := by
    rw [← hf']
    exact ker_polynomialTensorMap_algEquiv C _ eA
  rw [hkerC, hker, ker_polynomialTensorMap_rename C q eT,
    ker_comp_renameEquiv q eT, hq, Ideal.map_map, Ideal.map_map]
  have hc : (MvPolynomial.renameEquiv C eT.symm).toRingHom.comp
      (MvPolynomial.map (algebraMap R C)) =
      (MvPolynomial.map (algebraMap R C)).comp
        (MvPolynomial.renameEquiv R eT.symm).toRingHom := by
    apply RingHom.ext
    intro p
    exact (MvPolynomial.map_rename (algebraMap R C) eT.symm p).symm
  rw [hc]

end

end GroupActions
