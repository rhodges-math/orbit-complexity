import OrbitComplexity.GroupActions.Rosenlicht.RestrictedInvariants

/-!
# Lifts into invariant domains

Open subsets contained in the invariant domain map to that domain, compatibly with the
ambient inclusion and the invariant morphism.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- Every open contained in the invariant domain maps to that domain over
the base field. -/
def invariantDomainLift (U : X.scheme.Opens) (hUD : U ≤ (invariantMap H X).domain) :
    (X.openSubvariety U).toOver ⟶ (invariantDomain H X).toOver := by
  let D := (invariantMap H X).domain
  refine Over.homMk (X.scheme.homOfLE hUD) ?_
  change X.scheme.homOfLE hUD ≫ (D.ι ≫ X.toSpec) = U.ι ≫ X.toSpec
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- The lift to the invariant domain recovers the ambient open inclusion. -/
theorem invariantDomainLift_inclusion (U : X.scheme.Opens)
    (hUD : U ≤ (invariantMap H X).domain) :
    invariantDomainLift H X U hUD ≫ X.openInclusion (invariantMap H X).domain =
      X.openInclusion U := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.scheme hUD

/-- Composing the open-domain lift with the invariant morphism gives its
restriction to that open. -/
theorem invariantDomainLift_morphism (U : X.scheme.Opens)
    (hUD : U ≤ (invariantMap H X).domain) :
    invariantDomainLift H X U hUD ≫ invariantMorphism H X =
      invariantMorphismOn H X U hUD := by
  apply Over.OverMorphism.ext
  rfl

/-- The lift of a nonempty open subset to the invariant domain is dominant. -/
instance invariantDomainLift_dominant (U : X.scheme.Opens)
    (hUD : U ≤ (invariantMap H X).domain) [Nonempty U] :
    IsDominant (invariantDomainLift H X U hUD).left := by
  let D := (invariantMap H X).domain
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : Nonempty D := Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  have : IsIntegral D.toScheme := isIntegral_of_isOpenImmersion D.ι
  change IsDominant (X.scheme.homOfLE hUD)
  exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (X.scheme.homOfLE hUD)
    (X.scheme.homOfLE hUD).isOpenEmbedding.isOpenMap⟩

end

end GroupActions.Variety
