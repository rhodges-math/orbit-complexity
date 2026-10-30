import OrbitComplexity.GroupActions.Rosenlicht.RationalCharts

/-!
# Common regular charts for rational polynomial coefficients
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u v

/-- Finitely many rational polynomials have regular coefficients on a common
affine neighborhood of the generic point. -/
theorem exists_affine_polynomialChart (X : Scheme.{u}) [IrreducibleSpace X]
    {ι : Type v} (P : Finset (MvPolynomial ι X.functionField)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∃ hU : genericPoint X ∈ U,
      ∃ s : Finset (MvPolynomial ι Γ(X, U)),
        MvPolynomial.map (X.presheaf.germ U (genericPoint X) hU).hom ''
          (s : Set (MvPolynomial ι Γ(X, U))) = (P : Set (MvPolynomial ι X.functionField)) := by
  classical
  let C : Finset X.functionField := P.biUnion fun p ↦ p.support.image p.coeff
  have hC0 : (0 : X.functionField) ∉ C := by
    intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hp
    exact (MvPolynomial.mem_support_iff.mp hm) he
  obtain ⟨U, hUa, hU, c, hc⟩ := exists_affine_rationalChart X (fun a : C ↦ a.val)
  let r : X.functionField → Γ(X, U) := fun a ↦ if h : a ∈ C then c ⟨a, h⟩ else 0
  have hr0 : r 0 = 0 := dite_eq_right hC0
  let lift : MvPolynomial ι X.functionField → MvPolynomial ι Γ(X, U) :=
    fun p ↦ .ofCoeff (Finsupp.mapRange r hr0 p.coeff)
  have hlift (p : MvPolynomial ι X.functionField) (hp : p ∈ P) :
      MvPolynomial.map (X.presheaf.germ U (genericPoint X) hU).hom (lift p) = p := by
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_map]
    change X.presheaf.germ U (genericPoint X) hU (r (p.coeff m)) = p.coeff m
    by_cases hz : p.coeff m = 0
    · rw [hz, hr0, map_zero]
    · have hm : p.coeff m ∈ C :=
        Finset.mem_biUnion.mpr ⟨p, hp,
          Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hz, rfl⟩⟩
      dsimp only [r]
      rw [dite_eq_left hm]
      exact hc ⟨p.coeff m, hm⟩
  refine ⟨U, hUa, hU, P.image lift, ?_⟩
  apply Set.ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [hlift p hp]
    exact hp
  · intro hp
    exact ⟨lift p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hlift p hp⟩

end

end GroupActions
