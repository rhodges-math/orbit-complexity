import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Proper
import OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

/-! # Normal local rings on split scalar fibres

Properness and geometric connectedness persist under scalar extension of
an endpoint. An integral source fibre then gives an irreducible target,
so a Frobenius splitting and normal source stalks give normal target stalks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting

namespace SchubertGeometry

universe u

open private scalar_property from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

/-- A split scalar fibre of a proper geometrically connected endpoint has
normal domain stalks when its source fibre is integral with normal stalks. -/
theorem scalar_fibre_stalks {B : Scheme.{u}} (C D : Over B)
    [LocallyOfFiniteType D.hom] (e : C ⟶ D)
    [IsProper e.left] [GeometricallyConnected e.left]
    {L : Type u} [Field L] (s : Spec (.of L) ⟶ B)
    [IsIntegral (pullback s C.hom : Scheme.{u})]
    (hn : ∀ x : (pullback s C.hom : Scheme.{u}),
      IsIntegrallyClosed ((pullback s C.hom : Scheme.{u}).presheaf.stalk x))
    {q : ℕ} [Fact q.Prime] [CharP L q]
    (splitting : SchemeSplitting (pullback s D.hom) q) :
    ∀ y : (pullback s D.hom : Scheme.{u}),
      IsDomain ((pullback s D.hom : Scheme.{u}).presheaf.stalk y) ∧
      IsIntegrallyClosed ((pullback s D.hom : Scheme.{u}).presheaf.stalk y) := by
  let f : (pullback s C.hom : Scheme.{u}) ⟶
      (pullback s D.hom : Scheme.{u}) := (chosenScalarArrow s e).left
  let : IsProper f := scalar_property @IsProper s e inferInstance
  let : GeometricallyConnected f :=
    scalar_property @GeometricallyConnected s e inferInstance
  let : IrreducibleSpace (pullback s D.hom : Scheme.{u}) :=
    Function.Surjective.irreducibleSpace f.continuous f.surjective
  exact stalks_of_proper (pullback.fst s D.hom) f splitting hn

end SchubertGeometry
