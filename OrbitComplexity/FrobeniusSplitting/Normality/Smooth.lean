import OrbitComplexity.FrobeniusSplitting.Normality.SmoothBase

/-!
# Normal local rings of smooth schemes

Standard étale coordinates reduce smooth local rings over a field to local
localizations of étale polynomial algebras. Their generic total quotient rings
are reduced and Artinian, giving both the domain and integral-closedness properties.
-/

namespace FrobeniusSplitting

/-- Local rings of smooth algebras over a field are normal domains. -/
theorem localRings_of_smooth {K S B : Type*} [Field K] [CommRing S]
    [Algebra K S] [Algebra.Smooth K S] [CommRing B] [IsLocalRing B]
    [Algebra S B] (P : Ideal S) [P.IsPrime] [IsLocalization P.primeCompl B] :
    IsDomain B ∧ IsIntegrallyClosed B :=
  localRings_of_smooth_base (R := K) P



open AlgebraicGeometry CategoryTheory
universe u

/-- Smooth schemes over a field have normal local rings. -/
theorem stalks_of_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] :
    ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let e := Scheme.ΓSpecIso (.of K)
  let ψ : K →+* Γ(X, U) := (f.appLE ⊤ U le_top).hom.comp e.inv.hom
  have hψ : ψ.Smooth :=
    (RingHom.Smooth.of_bijective e.symm.commRingCatIsoToRingEquiv.bijective).comp
      (f.smooth_appLE (isAffineOpen_top _) hU le_top)
  let : Algebra K Γ(X, U) := ψ.toAlgebra
  have : Algebra.Smooth K Γ(X, U) := hψ.toAlgebra
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact localRings_of_smooth (K := K) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal

end FrobeniusSplitting
