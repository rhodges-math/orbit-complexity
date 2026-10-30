import OrbitComplexity.GroupActions.Rosenlicht.SaturatedFibres
import OrbitComplexity.GroupActions.Rosenlicht.RestrictedInvariants

/-!
# Invariant morphisms with orbit fibres

A saturated separating open subset inherits the algebraic group action, and the restricted
invariant morphism has precisely its point orbits as fibres.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A saturated nonempty open subvariety has a dominant invariant morphism
whose rational-point fibres are precisely its group orbits. -/
theorem exists_saturated_orbit_morphism :
    ∃ U : X.scheme.Opens, (U : Set X.scheme).Nonempty ∧
      ∃ hUD : saturationOpen H X U ≤ (invariantMap H X).domain,
        letI := saturationAction H X U
        ∀ x y : (X.openSubvariety (saturationOpen H X U)).points,
          mapPoints (invariantMorphismOn H X _ hUD) x =
            mapPoints (invariantMorphismOn H X _ hUD) y ↔
              y ∈ MulAction.orbit H.points x := by
  obtain ⟨U, hU, hUD, hsep⟩ := exists_saturated_invariant_fibres H X
  let s := saturationOpen H X U
  let S := X.openSubvariety s
  let : ModObj H.toOver S.toOver := saturationAction H X U
  let i : S.toOver ⟶ X.toOver := X.openInclusion s
  let f : S.toOver ⟶ (invariantModel H X).toOver := invariantMorphismOn H X s hUD
  let D := (invariantMap H X).domain
  let q : D.toScheme ⟶ (invariantModel H X).scheme := (invariantMorphism H X).left
  have hval (z : S.points) :
      (invariantModel H X).pointMap (mapPoints f z) =
        q ⟨X.pointMap (mapPoints i z), by
          apply hUD
          exact (S.pointMap z).property⟩ := by
    let z' : s.toScheme := S.pointMap z
    change q (X.scheme.homOfLE hUD z') = _
    apply congrArg q
    apply Subtype.ext
    exact Scheme.homOfLE_apply hUD z'
  have himg (z : S.points) : X.pointMap (mapPoints i z) ∈ s :=
    (S.pointMap z).property
  have horbits (x y : S.points) :
      mapPoints i y ∈ MulAction.orbit H.points (mapPoints i x) ↔
        y ∈ MulAction.orbit H.points x := by
    constructor
    · intro h
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g, ?_⟩
      apply mapPoints_injective_of_mono i
      exact (saturationAction_smul H X U g x).trans hg
    · intro h
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨g, (saturationAction_smul H X U g x).symm⟩
  refine ⟨U, hU, hUD, ?_⟩
  intro x y
  change mapPoints f x = mapPoints f y ↔ y ∈ MulAction.orbit H.points x
  constructor
  · intro h
    apply (horbits x y).mp
    apply (hsep (mapPoints i x) (mapPoints i y) (himg x) (himg y)).mp
    exact (hval x).symm.trans ((congrArg (invariantModel H X).pointMap h).trans (hval y))
  · intro h
    have hh := (hsep (mapPoints i x) (mapPoints i y) (himg x) (himg y)).mpr
      ((horbits x y).mpr h)
    apply (invariantModel H X).pointMap_injective
    exact (hval x).trans (hh.trans (hval y).symm)

end

end GroupActions.Variety
