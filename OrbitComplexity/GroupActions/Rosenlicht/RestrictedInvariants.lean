import OrbitComplexity.GroupActions.Rosenlicht.InvariantDomains

/-!
# Restrictions of invariant morphisms

The invariant morphism restricts to open subsets of its domain, and nonempty restrictions
remain dominant.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- The invariant morphism restricts to every open subset of its domain. -/
def invariantMorphismOn (U : X.scheme.Opens) (hUD : U ≤ (invariantMap H X).domain) :
    (X.openSubvariety U).toOver ⟶ (invariantModel H X).toOver := by
  let D := (invariantMap H X).domain
  let f : D.toScheme ⟶ (invariantModel H X).scheme := (invariantMorphism H X).left
  refine Over.homMk (X.scheme.homOfLE hUD ≫ f) ?_
  have hf : f ≫ (invariantModel H X).toSpec = D.ι ≫ X.toSpec :=
    (invariantMorphism H X).w
  change (X.scheme.homOfLE hUD ≫ f) ≫ (invariantModel H X).toSpec = U.ι ≫ X.toSpec
  rw [Category.assoc, hf, ← Category.assoc, Scheme.homOfLE_ι]

/-- Restriction of the invariant morphism to a nonempty open remains dominant. -/
instance invariantMorphismOn_dominant (U : X.scheme.Opens)
    (hUD : U ≤ (invariantMap H X).domain) [Nonempty U] :
    IsDominant (invariantMorphismOn H X U hUD).left := by
  let D := (invariantMap H X).domain
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : Nonempty D := Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  have : IsIntegral D.toScheme := isIntegral_of_isOpenImmersion D.ι
  have : IsDominant (X.scheme.homOfLE hUD) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (X.scheme.homOfLE hUD)
      (X.scheme.homOfLE hUD).isOpenEmbedding.isOpenMap⟩
  let f : D.toScheme ⟶ (invariantModel H X).scheme := (invariantMorphism H X).left
  have : IsDominant f := invariantMorphism_dominant H X
  change IsDominant (X.scheme.homOfLE hUD ≫ f)
  infer_instance

end

end GroupActions.Variety
