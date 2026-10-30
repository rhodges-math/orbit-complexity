import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.SchubertGeometry.Groups.WeylQuotient
import OrbitComplexity.SchubertGeometry.FlagVariety.PointTopology
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Flag, Schubert, Richardson, and algebraic-action definitions

Each clause below is proved from the scheme constructions and their rational-point maps.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open ReductiveGroups SchubertGeometry GroupActions GroupActions.Variety
open scoped CategoryTheory.MonObj

noncomputable section
universe u
namespace SchubertOrbits.FlagDefinitions

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The chosen reductive group, subgroups, and Weyl normalizer quotient. -/
def groupClauses (G : ReductiveGroupData K) : Prop :=
  ConnectedSpace (reductiveVariety G).scheme ∧
  TauCeti.reductiveCommHopfAlgProperty K G.coordinateAlgebra ∧
  TauCeti.HopfIdeal.IsMaximalTorus K
    (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal ∧
  TauCeti.HopfIdeal.IsBorel K
    (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal ∧
  G.torusPoints ≤ G.borelPoints ∧
  TauCeti.HopfIdeal.IsBorel K
    (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal ∧
  (∀ x : G.points, G.longestPoint * x * G.longestPoint⁻¹ ∈ G.oppositeBorelPoints ↔
    x ∈ G.borelPoints) ∧
  ∃ e : G.weylGroup ≃* G.torusNormalizer ⧸ G.torusInNormalizer,
    ∀ w, e w = QuotientGroup.mk
      (⟨G.weylPoint w, G.weylPoint_mem_normalizer w⟩ : G.torusNormalizer)

/-- The full flag variety has the quotient points and quotient Zariski topology. -/
def quotientClauses (G : ReductiveGroupData K) : Prop :=
  ∃ e : flagPoints G ≃ₜ (flagVariety G).points,
    (∀ g : G.points,
      mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G g) =
        e (flagProjection G g)) ∧
    Surjective (flagQuotientMorphism G).left ∧
    ∀ g h : G.points,
      mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G g) =
          mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G h) ↔
        g⁻¹ * h ∈ G.borelPoints

/-- Schubert cells are Borel orbits, and Schubert varieties are their closures. -/
def strataClauses (G : ReductiveGroupData K) : Prop :=
  ∀ w : G.weylGroup,
    weylFlagPoint G w = flagVarietyPointsEquiv G (flagProjection G (G.weylPoint w)) ∧
    Set.range (mapPoints (schubertCellInclusion G w)) =
        MulAction.orbit (borelVariety G).points (weylFlagPoint G w) ∧
    Set.range (schubertInclusion G w).left =
        closure (Set.range (schubertCellInclusion G w).left) ∧
    Set.range (mapPoints (oppositeSchubertCellInclusion G w)) =
        MulAction.orbit (oppositeBorelVariety G).points (weylFlagPoint G w) ∧
    Set.range (oppositeSchubertInclusion G w).left =
        closure (Set.range (oppositeSchubertCellInclusion G w).left)

/-- Closed and open Richardson varieties have the prescribed intersection images. -/
def intersectionClauses (G : ReductiveGroupData K) : Prop :=
  ∀ v w : G.weylGroup,
    Set.range (richardsonInclusion G v w).left =
        Set.range (schubertInclusion G w).left ∩
          Set.range (oppositeSchubertInclusion G v).left ∧
    Set.range (mapPoints (richardsonInclusion G v w)) =
        Set.range (mapPoints (schubertInclusion G w)) ∩
          Set.range (mapPoints (oppositeSchubertInclusion G v)) ∧
    Set.range (richardsonCellInclusion G v w).left =
        Set.range (schubertCellInclusion G w).left ∩
          Set.range (oppositeSchubertCellInclusion G v).left ∧
    Set.range (mapPoints (richardsonCellInclusion G v w)) =
        Set.range (mapPoints (schubertCellInclusion G w)) ∩
          Set.range (mapPoints (oppositeSchubertCellInclusion G v))

/-- Group morphisms and invariant subvarieties inherit the usual left flag action. -/
def subgroupClauses (G : ReductiveGroupData K) : Prop :=
  ∀ (H : Variety K) [GrpObj H.toOver]
    (f : H.toOver ⟶ (reductiveVariety G).toOver) [IsMonHom f],
    letI := Mod.scalarRestriction f (flagVariety G).toOver
    (∀ (h : H.points) (x : flagPoints G),
      h • flagVarietyPointsEquiv G x = flagVarietyPointsEquiv G
        (((reductivePointsMulEquiv G).symm (mapPoints f h)) • x)) ∧
    ∀ (Y : Variety K) (i : Y.toOver ⟶ (flagVariety G).toOver)
      [IsPreimmersion i.left]
      (hstable : ∀ (h : H.points) (y : Y.points),
        h • mapPoints i y ∈ Set.range (mapPoints i)),
      letI := modObjOfInvariant H (flagVariety G) Y i hstable
      IsModHom H.toOver i ∧
      ∀ (h : H.points) (y : Y.points), mapPoints i (h • y) = h • mapPoints i y

/-- Every subgroup of rational points inherits the usual left action on flag cosets. -/
def pointSubgroupClauses (G : ReductiveGroupData K) : Prop :=
  ∀ S : Subgroup G.points,
    letI : MulAction S (flagPoints G) := MulAction.compHom (flagPoints G) S.subtype
    ∀ (s : S) (x : flagPoints G), s • x = (s : G.points) • x

/-- An algebraic group action is a variety morphism satisfying the action identities. -/
def actionClauses (K : Type u) [Field K] : Prop :=
  ∀ (H X : Variety K) [GrpObj H.toOver],
    Nonempty (ModObj H.toOver X.toOver) ↔
      ∃ a : H.toOver ⊗ X.toOver ⟶ X.toOver,
        (η[H.toOver] ▷ X.toOver) ≫ a = (λ_ X.toOver).hom ∧
        (μ[H.toOver] ▷ X.toOver) ≫ a =
          (α_ H.toOver H.toOver X.toOver).hom ≫ (H.toOver ◁ a) ≫ a

/-- The orbit quotient is identified with the set of orbits of rational points. -/
def orbitClauses (K : Type u) [Field K] : Prop :=
  ∀ (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver],
    Function.Injective (MulAction.orbitRel.Quotient.orbit :
      MulAction.orbitRel.Quotient H.points X.points → Set X.points) ∧
    Set.range (MulAction.orbitRel.Quotient.orbit :
      MulAction.orbitRel.Quotient H.points X.points → Set X.points) =
        Set.range (MulAction.orbit H.points : X.points → Set X.points) ∧
    ∀ x : X.points,
      MulAction.orbitRel.Quotient.orbit
          (Quotient.mk'' x : MulAction.orbitRel.Quotient H.points X.points) =
        MulAction.orbit H.points x

/-- All flag, Schubert, Richardson, and action definition clauses over the chosen field. -/
def flagDefinitions (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] : Prop :=
  (∀ G : ReductiveGroupData K,
    groupClauses G ∧ quotientClauses G ∧ strataClauses G ∧
      intersectionClauses G ∧ subgroupClauses G ∧ pointSubgroupClauses G) ∧
      actionClauses K ∧ orbitClauses K

private theorem groupProof (G : ReductiveGroupData K) : groupClauses G := by
  exact ⟨inferInstance, G.reductive, G.isMaximalTorus, G.isBorel, G.torus_le_borel,
    G.oppositeBorel_isBorel, G.conj_mem_oppositeBorel,
    weylQuotientEquiv G, weylQuotientEquiv_apply G⟩

private theorem quotientProof (G : ReductiveGroupData K) : quotientClauses G := by
  refine ⟨flagVarietyPointsHomeomorph G, flagQuotientMorphism_points G, ?_, ?_⟩
  · exact inferInstanceAs (Surjective (flagQuotient G))
  · intro g h
    rw [flagQuotientMorphism_points, flagQuotientMorphism_points,
      (flagVarietyPointsEquiv G).injective.eq_iff, flagProjection_eq_iff]

private theorem strataProof (G : ReductiveGroupData K) : strataClauses G := by
  intro w
  exact ⟨rfl, schubertCell_points_range G w, schubertInclusion_range G w,
    oppositeSchubertCell_points_range G w, oppositeSchubertInclusion_range G w⟩

private theorem intersectionProof (G : ReductiveGroupData K) :
    intersectionClauses G := by
  intro v w
  exact ⟨richardsonInclusion_range G v w, richardson_points_range G v w,
    richardsonCellInclusion_range G v w, richardsonCell_points_range G v w⟩

private theorem subgroupProof (G : ReductiveGroupData K) : subgroupClauses G := by
  intro H _ f _
  let := Mod.scalarRestriction f (flagVariety G).toOver
  constructor
  · intro h x
    rw [restricted_smul]
    simpa only [MulEquiv.apply_symm_apply] using
      flagVarietyAction_points G ((reductivePointsMulEquiv G).symm (mapPoints f h)) x
  · intro Y i _ hstable
    exact ⟨modObjOfInvariant_isModHom H (flagVariety G) Y i hstable,
      modObjOfInvariant_smul H (flagVariety G) Y i hstable⟩

omit [IsAlgClosed K] [CharZero K] in
private theorem pointSubgroupProof (G : ReductiveGroupData K) : pointSubgroupClauses G := by
  intro S s x
  rfl

private theorem actionProof (K : Type u) [Field K] : actionClauses K := by
  intro H X _
  constructor
  · rintro ⟨a⟩
    let := a
    exact ⟨ModObj.smul (M := H.toOver),
      ModObj.one_smul (M := H.toOver) X.toOver,
      ModObj.mul_smul (M := H.toOver) X.toOver⟩
  · rintro ⟨a, hu, hm⟩
    exact ⟨{ smul := a, one_smul := hu, mul_smul := hm }⟩

private theorem orbitProof (K : Type u) [Field K] : orbitClauses K := by
  intro H X _ _
  refine ⟨MulAction.orbitRel.Quotient.orbit_injective, ?_,
    MulAction.orbitRel.Quotient.orbit_mk⟩
  ext S
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Quotient.mk'' x, rfl⟩

/-- The defining properties follow from the scheme constructions. -/
private theorem flagDefinitions_proved : flagDefinitions K := by
  exact ⟨fun G => ⟨groupProof G, quotientProof G, strataProof G,
    intersectionProof G, subgroupProof G, pointSubgroupProof G⟩, actionProof K, orbitProof K⟩

/-- The same complete conjunction in the complex field used for the geometric objects. -/
def flagDefinitionsComplex : Prop :=
  (∀ G : ReductiveGroupData ℂ,
    groupClauses G ∧ quotientClauses G ∧ strataClauses G ∧
      intersectionClauses G ∧ subgroupClauses G ∧ pointSubgroupClauses G) ∧
      actionClauses ℂ ∧ orbitClauses ℂ


end SchubertOrbits.FlagDefinitions

namespace SchubertOrbits

/-- The full flag variety, its Schubert and Richardson strata, and left actions have their
quotient, orbit, closure and intersection descriptions. -/
theorem flag_variety_definitions {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] :
    FlagDefinitions.flagDefinitions K :=
  FlagDefinitions.flagDefinitions_proved

/-- The flag, Schubert, Richardson and action definitions hold over the complex numbers. -/
theorem flag_varieties_complex : FlagDefinitions.flagDefinitionsComplex :=
  FlagDefinitions.flagDefinitions_proved (K := ℂ)

end SchubertOrbits
