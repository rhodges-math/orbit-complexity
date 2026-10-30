import OrbitComplexity.GroupActions.Rosenlicht.SurjectiveOrbitMorphism
import OrbitComplexity.GroupActions.Rosenlicht.QuotientFields

/-!
# Rational orbit quotients

An irreducible algebraic group action has a surjective orbit quotient on a nonempty stable
open subvariety, with the prescribed invariant-function-field pullback.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- An irreducible algebraic group action admits a surjective orbit quotient on
a nonempty stable open subvariety. Its function-field pullback identifies the
quotient's rational functions with the invariant rational functions. -/
theorem exists_orbit_quotient :
    ∃ V : (invariantModel H X).scheme.Opens,
      ∃ hV : (V : Set (invariantModel H X).scheme).Nonempty,
      letI : Nonempty V := Set.nonempty_coe_sort.mpr hV
      ∃ Z : GroupActions.Variety K, Nonempty Z.scheme ∧
        ∃ hZ : IrreducibleSpace Z.scheme,
          letI := hZ
          ∃ M : ModObj H.toOver Z.toOver,
            letI := M
            ∃ i : Z.toOver ⟶ X.toOver,
              IsOpenImmersion i.left ∧ IsDominant i.left ∧ IsModHom H.toOver i ∧
              ∃ q : Z.toOver ⟶ ((invariantModel H X).openSubvariety V).toOver,
                ∃ hq : Surjective q.left,
                letI := hq
                (∀ x y : Z.points, mapPoints q x = mapPoints q y ↔
                  y ∈ MulAction.orbit H.points x) ∧
                letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
                letI : Z.scheme.Over (Spec (.of K)) := ⟨Z.toSpec⟩
                letI : IsIntegral X.scheme :=
                  isIntegral_of_irreducibleSpace_of_isReduced X.scheme
                letI : IsIntegral Z.scheme :=
                  isIntegral_of_irreducibleSpace_of_isReduced Z.scheme
                letI : (invariantModel H X).scheme.Over (Spec (.of K)) :=
                  ⟨(invariantModel H X).toSpec⟩
                letI : ((invariantModel H X).openSubvariety V).scheme.Over
                    (Spec (.of K)) := ⟨((invariantModel H X).openSubvariety V).toSpec⟩
                letI : IsIntegral ((invariantModel H X).openSubvariety V).scheme := by
                  have : IsOpenImmersion V.ι :=
                    (invariantModel H X).openInclusion_isOpenImmersion V
                  exact (show IsIntegral V.toScheme from isIntegral_of_isOpenImmersion V.ι)
                ∃ e : ((invariantModel H X).openSubvariety V).scheme.functionField ≃ₐ[K]
                    invariantField H Z,
                  ∀ a, (e a).val = functionFieldMap (X := Z.scheme)
                    (Y := ((invariantModel H X).openSubvariety V).scheme) q.left a := by
  obtain ⟨V, hV, Z, hZne, hZirr, M, i, hiOpen, hiDom, hiMod,
    d, hdDom, hdi, q, hq, hqd, hquot⟩ := exists_surjective_orbit_morphism H X
  have : Nonempty V := Set.nonempty_coe_sort.mpr hV
  have : Nonempty Z.scheme := hZne
  have : IrreducibleSpace Z.scheme := hZirr
  let : ModObj H.toOver Z.toOver := M
  have : IsOpenImmersion i.left := hiOpen
  have : IsDominant i.left := hiDom
  have : IsModHom H.toOver i := hiMod
  have : IsDominant d.left := hdDom
  have : Surjective q.left := hq
  refine ⟨V, hV, Z, hZne, hZirr, M, i, hiOpen, hiDom, hiMod, q, hq, hquot, ?_⟩
  exact ⟨invariantOpenFieldEquiv H X Z V i,
    invariantOpenFieldEquiv_apply H X Z V i d q hdi hqd⟩

end

end GroupActions.Variety
