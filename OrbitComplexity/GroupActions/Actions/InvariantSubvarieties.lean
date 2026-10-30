import OrbitComplexity.GroupActions.Actions.FromPoints
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Algebraic actions on invariant subvarieties

A reduced preimmersion whose rational-point image is invariant inherits the ambient
algebraic group action. Constructibility detects scheme image containment from rational
points, and the reduced product factors through the preimmersion.

## Main definitions

* `GroupActions.Variety.modObjOfInvariant`: the inherited algebraic action.

## Main results

* `GroupActions.Variety.modObjOfInvariant_isModHom`: the preimmersion is equivariant.
* `GroupActions.Variety.modObjOfInvariant_smul`: its rational-point action formula.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem groupSmooth (H : GroupActions.Variety K) [GrpObj H.toOver] :
    Smooth H.toSpec :=
  TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced H.toSpec

attribute [local instance] groupSmooth

variable (H X Y : GroupActions.Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]
  (i : Y.toOver ⟶ X.toOver) [IsPreimmersion i.left]
  (hstable : ∀ (h : H.points) (y : Y.points),
    h • mapPoints i y ∈ Set.range (mapPoints i))

include hstable in
omit [IsPreimmersion i.left] in
private theorem invariantImage :
    Set.range (((H.toOver ◁ i) ≫ γ[H.toOver, X.toOver]).left :
      (smoothProductVariety H Y).scheme → X.scheme) ⊆ Set.range (i.left : Y.scheme → X.scheme) := by
  apply range_subset_of_mapPoints (A := smoothProductVariety H Y) (B := Y) (C := X)
    ((H.toOver ◁ i) ≫ γ[H.toOver, X.toOver]) i
  rintro z ⟨p, rfl⟩
  let q := (smoothProductVariety H Y).pointsEquivOverHom p
  let h := H.pointsEquivOverHom.symm (q ≫ fst H.toOver Y.toOver)
  let y := Y.pointsEquivOverHom.symm (q ≫ snd H.toOver Y.toOver)
  have hq : q = lift (H.pointsEquivOverHom h) (Y.pointsEquivOverHom y) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [lift_fst, lift_snd, h, y, Equiv.apply_symm_apply]
  have hp : mapPoints ((H.toOver ◁ i) ≫ γ[H.toOver, X.toOver]) p =
      h • mapPoints i y := by
    apply X.pointsEquivOverHom.injective
    rw [pointsEquivOverHom_smul]
    change q ≫ ((H.toOver ◁ i) ≫ γ[H.toOver, X.toOver]) =
      H.pointsEquivOverHom h • X.pointsEquivOverHom (mapPoints i y)
    rw [hq, lift_whiskerLeft_assoc]
    rfl
  rw [hp]
  exact hstable h y

private def invariantActionMorphism :
    H.toOver ⊗ Y.toOver ⟶ Y.toOver := by
  let P : GroupActions.Variety K := smoothProductVariety H Y
  have : IsReduced P.scheme := P.reduced
  let f : P.toOver ⟶ X.toOver := (H.toOver ◁ i) ≫ γ[H.toOver, X.toOver]
  let f₀ : P.scheme ⟶ X.scheme := f.left
  let i₀ : Y.scheme ⟶ X.scheme := i.left
  have hr : Set.range f₀ ⊆ Set.range i₀ := invariantImage H X Y i hstable
  let g₀ : P.scheme ⟶ Y.scheme := GroupActions.liftPreimmersion i₀ f₀ hr
  have hg : g₀ ≫ i₀ = f₀ := GroupActions.liftPreimmersion_fac i₀ f₀ hr
  exact Over.homMk g₀ (by
    change g₀ ≫ Y.toSpec = P.toSpec
    rw [← (show i₀ ≫ X.toSpec = Y.toSpec from i.w), ← Category.assoc, hg]
    exact f.w)

private theorem invariantAction_fac :
    invariantActionMorphism H X Y i hstable ≫ i =
      (H.toOver ◁ i) ≫ γ[H.toOver, X.toOver] := by
  apply Over.OverMorphism.ext
  let P : GroupActions.Variety K := smoothProductVariety H Y
  have : IsReduced P.scheme := P.reduced
  let f₀ : P.scheme ⟶ X.scheme :=
    ((H.toOver ◁ i) ≫ γ[H.toOver, X.toOver]).left
  let i₀ : Y.scheme ⟶ X.scheme := i.left
  change GroupActions.liftPreimmersion i₀ f₀ (invariantImage H X Y i hstable) ≫ i₀ = f₀
  exact GroupActions.liftPreimmersion_fac i₀ f₀ _

@[instance_reducible]
private def invariantPointAction : MulAction H.points Y.points := by
  letI : SMul H.points Y.points := ⟨fun h y => (hstable h y).choose⟩
  exact Function.Injective.mulAction (mapPoints i) (mapPoints_injective_of_mono i)
    (fun h y => (hstable h y).choose_spec)

omit [IsAlgClosed K] in
private theorem invariantPointAction_map (h : H.points) (y : Y.points) :
    letI := invariantPointAction H X Y i hstable
    mapPoints i (h • y) = h • mapPoints i y :=
  (hstable h y).choose_spec

/-- An invariant reduced preimmersion inherits the ambient algebraic group action. -/
@[instance_reducible]
def modObjOfInvariant : ModObj H.toOver Y.toOver := by
  letI := invariantPointAction H X Y i hstable
  refine modObjOfPoints H Y (invariantActionMorphism H X Y i hstable) ?_
  intro h y
  have : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  rw [Category.assoc, invariantAction_fac, lift_whiskerLeft_assoc]
  change H.pointsEquivOverHom h • X.pointsEquivOverHom (mapPoints i y) =
    X.pointsEquivOverHom (mapPoints i (h • y))
  rw [← pointsEquivOverHom_smul, invariantPointAction_map]

/-- The inherited action makes the preimmersion equivariant. -/
theorem modObjOfInvariant_isModHom :
    let := modObjOfInvariant H X Y i hstable
    IsModHom H.toOver i := by
  let := modObjOfInvariant H X Y i hstable
  constructor
  exact invariantAction_fac H X Y i hstable

/-- The inherited action on rational points commutes with the preimmersion. -/
theorem modObjOfInvariant_smul (h : H.points) (y : Y.points) :
    let := modObjOfInvariant H X Y i hstable
    mapPoints i (h • y) = h • mapPoints i y := by
  let := modObjOfInvariant H X Y i hstable
  let := modObjOfInvariant_isModHom H X Y i hstable
  apply X.pointsEquivOverHom.injective
  change Y.pointsEquivOverHom (h • y) ≫ i =
    X.pointsEquivOverHom (h • mapPoints i y)
  rw [pointsEquivOverHom_smul, pointsEquivOverHom_smul]
  exact IsModHom.map_smul i (H.pointsEquivOverHom h) (Y.pointsEquivOverHom y)

end

end GroupActions.Variety
