import OrbitComplexity.GroupActions.Rosenlicht.LexSupport
import OrbitComplexity.GroupActions.Rosenlicht.PolynomialKernels
import OrbitComplexity.GroupActions.Rosenlicht.PolynomialBaseChange

/-!
# Specialization of elimination ideals

The map from the polynomial algebra on a final set of variables to a quotient
has complemented image when the defining ideal has a lexicographic leading
basis. Its relation ideal therefore commutes with coefficient extension.
-/

open MvPolynomial
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] {σ : Type v}

/-- The polynomial algebra on selected variables maps to a polynomial quotient
by renaming the variables and taking quotient classes. -/
def quotientVariableMap (I : Ideal (MvPolynomial σ R)) (t : Set σ) :
    MvPolynomial t R →ₐ[R] MvPolynomial σ R ⧸ I :=
  (Ideal.Quotient.mkₐ R I).comp (MvPolynomial.rename ((↑) : t → σ))

/-- A selected variable maps to its class in the ambient polynomial quotient. -/
@[simp]
theorem quotientVariableMap_X (I : Ideal (MvPolynomial σ R)) (t : Set σ) (i : t) :
    quotientVariableMap I t (X i) = Ideal.Quotient.mk I (X i.val) := by
  simp [quotientVariableMap]

/-- The image of the selected-variable map is the quotient image of the
variable-supported polynomial subalgebra. -/
theorem quotientVariableMap_range (I : Ideal (MvPolynomial σ R)) (t : Set σ) :
    LinearMap.range (quotientVariableMap I t).toLinearMap =
      ((MvPolynomial.supported R t).toSubmodule).map (I.restrictScalars R).mkQ := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨MvPolynomial.rename ((↑) : t → σ) p, ?_, rfl⟩
    change MvPolynomial.rename ((↑) : t → σ) p ∈ MvPolynomial.supported R t
    rw [MvPolynomial.supported_eq_range_rename]
    exact ⟨p, rfl⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := hz
    change p ∈ MvPolynomial.supported R t at hp
    rw [MvPolynomial.supported_eq_range_rename] at hp
    obtain ⟨q, rfl⟩ := hp
    exact ⟨q, rfl⟩

/-- The tensor extension of a selected-variable map has the same kernel as
the selected-variable map to the coefficient-extended polynomial quotient. -/
theorem ker_quotientVariableMap_tensor
    (S : Type w) [CommRing S] [Algebra R S]
    (I : Ideal (MvPolynomial σ R)) (t : Set σ) :
    RingHom.ker (quotientVariableMap (I.map (MvPolynomial.map (algebraMap R S))) t) =
      RingHom.ker (polynomialTensorMap S (quotientVariableMap I t)) := by
  let f := quotientVariableMap I t
  let e := polynomialQuotientBaseChange R S I
  have he : e.toAlgHom.comp (polynomialTensorMap S f) =
      quotientVariableMap (I.map (MvPolynomial.map (algebraMap R S))) t := by
    ext i
    change e (polynomialTensorMap S f (X i)) = _
    change e ((Algebra.TensorProduct.map (AlgHom.id S S) f)
      ((MvPolynomial.algebraTensorAlgEquiv R S).symm (X i))) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_X, Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.id_apply, f, quotientVariableMap_X]
    rw [polynomialQuotientBaseChange_tmul]
    simp only [MvPolynomial.map_X, one_smul]
  ext p
  change quotientVariableMap (I.map (MvPolynomial.map (algebraMap R S))) t p = 0 ↔
    polynomialTensorMap S f p = 0
  rw [← AlgHom.congr_fun he p]
  change e (polynomialTensorMap S f p) = 0 ↔ polynomialTensorMap S f p = 0
  constructor
  · intro hp
    apply e.injective
    simpa only [map_zero] using hp
  · intro hp
    simp only [hp, map_zero]

/-- For a final set of variables and a lexicographic leading basis, scalar
extension creates no additional polynomial relations in the selected variables. -/
theorem ker_quotientVariableMap_baseChange [LinearOrder σ] [WellFoundedGT σ]
    (S : Type w) [CommRing S] [Algebra R S]
    (s : Finset (MvPolynomial σ R))
    (hu : ∀ q ∈ s, IsUnit (MonomialOrder.lex.leadingCoeff q))
    (hd : ∀ p ∈ Ideal.span (s : Set (MvPolynomial σ R)), p ≠ 0 →
      ∃ q ∈ s, MonomialOrder.lex.degree q ≤ MonomialOrder.lex.degree p)
    (t : Set σ) (ht : IsUpperSet t) :
    let I := Ideal.span (s : Set (MvPolynomial σ R))
    RingHom.ker (quotientVariableMap (I.map (MvPolynomial.map (algebraMap R S))) t) =
      (RingHom.ker (quotientVariableMap I t)).map
        (MvPolynomial.map (algebraMap R S)) := by
  let I := Ideal.span (s : Set (MvPolynomial σ R))
  let f := quotientVariableMap I t
  have hC := isCompl_quotient_variables s hu hd t ht
  rw [← quotientVariableMap_range] at hC
  exact (ker_quotientVariableMap_tensor S I t).trans
    (ker_polynomialTensorMap S f _ hC)

/-- Flat coefficient extension preserves the full relation ideal of every
selected-variable map to a polynomial quotient. -/
theorem ker_quotientVariableMap_of_flat
    (S : Type w) [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal (MvPolynomial σ R)) (t : Set σ) :
    RingHom.ker (quotientVariableMap (I.map (MvPolynomial.map (algebraMap R S))) t) =
      (RingHom.ker (quotientVariableMap I t)).map
        (MvPolynomial.map (algebraMap R S)) :=
  (ker_quotientVariableMap_tensor S I t).trans
    (ker_polynomialTensorMap_of_flat S (quotientVariableMap I t))

end

end GroupActions
