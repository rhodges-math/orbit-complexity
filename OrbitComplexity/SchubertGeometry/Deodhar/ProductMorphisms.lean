import OrbitComplexity.SchubertGeometry.Deodhar.Products
import OrbitComplexity.GroupActions.Varieties.AdditiveVariety
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.SchubertGeometry.FlagVariety.Variety

/-! # Morphisms from selected-root coordinates

Each selected coordinate maps to its conjugated root subgroup. Their ordered product gives a
morphism from affine space to the reductive group. Multiplication by the signed representative
and projection to the flag variety give a flag-valued morphism with the same point formula.

## Main definitions and results

* `subwordProductMorphism`: the ordered root-product morphism for a prefix.
* `subwordProductMorphism_points`: its selected-coordinate point formula.
* `subwordFlagMorphism`: the product followed by its representative and flag projection.
* `subwordFlagMorphism_points`: its flag point formula.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Section 5.
-/
open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
namespace SchubertGeometry
open GroupActions GroupActions.Variety ReductiveGroups TauCeti SchubertGeometry BruhatIntervals
universe u

private theorem mapPoints_one {K : Type u} [Field K] {X H : Variety K}
    [GrpObj H.toOver] (x : X.points) : mapPoints (1 : X.toOver ⟶ H.toOver) x = 1 := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_one]
  change X.pointsEquivOverHom x ≫ (1 : X.toOver ⟶ H.toOver) = 1
  exact MonObj.comp_one _

private theorem mapPoints_mul {K : Type u} [Field K] {X H : Variety K}
    [GrpObj H.toOver] (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    mapPoints (f * g) x = mapPoints f x * mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

private def evaluatePoint {K : Type u} [Field K] {X H : Variety K} [GrpObj H.toOver]
    (x : X.points) : (X.toOver ⟶ H.toOver) →* H.points where
  toFun f := mapPoints f x
  map_one' := mapPoints_one x
  map_mul' f g := mapPoints_mul f g x

private theorem mapPoints_list_prod {K : Type u} [Field K] {X H : Variety K}
    [GrpObj H.toOver] (morphisms : List (X.toOver ⟶ H.toOver)) (x : X.points) :
    mapPoints morphisms.prod x = (morphisms.map (fun f => mapPoints f x)).prod :=
  (evaluatePoint x).map_list_prod morphisms

private def constantMorphism {K : Type u} [Field K] (X H : Variety K) (h : H.points) :
    X.toOver ⟶ H.toOver := toUnit X.toOver ≫ H.pointsEquivOverHom h

private theorem constantMorphism_points {K : Type u} [Field K] (X H : Variety K)
    (h : H.points) (x : X.points) : mapPoints (constantMorphism X H h) x = h := by
  apply H.pointsEquivOverHom.injective
  change X.pointsEquivOverHom x ≫ (toUnit X.toOver ≫ H.pointsEquivOverHom h) = _
  rw [comp_toUnit_assoc]
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) = 𝟙 _ := toUnit_unique _ _
  rw [hu, Category.id_comp]

private def coordinatePullback {K κ : Type u} [Field K] (j : κ) :
    SymmetricAlgebra K K →ₐ[K] MvPolynomial κ K :=
  SymmetricAlgebra.lift (LinearMap.toSpanSingleton K _ (MvPolynomial.X j))

private def coordinateMorphism {K κ : Type u} [Field K] [Finite κ] (j : κ) :
    (affineSpaceVariety K κ).toOver ⟶ (additiveVariety K).toOver :=
  affineMorphism (coordinatePullback j)

private theorem coordinateMorphism_points {K κ : Type u} [Field K] [Finite κ] (j : κ)
    (x : (affineSpaceVariety K κ).points) :
    mapPoints (coordinateMorphism j) x =
      additivePointsEquiv K (affineSpaceVarietyPointsEquiv K κ x j) := by
  obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K (MvPolynomial κ K)).symm.surjective x
  change mapPoints (X := affineVariety K (MvPolynomial κ K))
    (Y := affineVariety K (SymmetricAlgebra K K)) (affineMorphism (coordinatePullback j))
      ((affineVarietyPointsEquiv K (MvPolynomial κ K)).symm p) = _
  rw [affineMorphism_points]
  apply (additivePointsEquiv K).symm.injective
  rw [Equiv.symm_apply_apply]
  change Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv
    ((affineGroupPointsMulEquiv K (SymmetricAlgebra K K)).symm
      ((affineVarietyPointsEquiv K (SymmetricAlgebra K K)).symm
        (p.comp (coordinatePullback j))))) = _
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv]
  change ((affineVarietyPointsEquiv K (SymmetricAlgebra K K))
    ((affineVarietyPointsEquiv K (SymmetricAlgebra K K)).symm
      (p.comp (coordinatePullback j)))) (SymmetricAlgebra.ι K K 1) =
    ((affineVarietyPointsEquiv K (MvPolynomial κ K))
      ((affineVarietyPointsEquiv K (MvPolynomial κ K)).symm p)) (MvPolynomial.X j)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [AlgHom.comp_apply, coordinatePullback, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply, one_smul]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

local notation "Positions" => {position : Fin word.length //
  position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
    negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}
private def rootCoordinateMorphism (j : Positions) :
    (affineSpaceVariety K (ULift.{u} Positions)).toOver ⟶ (reductiveVariety G).toOver :=
  coordinateMorphism (ULift.up j : ULift.{u} Positions) ≫
    gaMorphism G (subwordRootMap G expression j)

private theorem rootCoordinateMorphism_points (j : Positions)
    (x : (affineSpaceVariety K (ULift.{u} Positions)).points) :
    mapPoints (rootCoordinateMorphism G expression j) x =
      reductivePointsEquiv G (gaParameterPoint (subwordRootMap G expression j)
        (affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩)) := by
  exact (mapPoints_comp
    (coordinateMorphism (ULift.up j : ULift.{u} Positions))
    (gaMorphism G (subwordRootMap G expression j)) x).trans
      ((congrArg (mapPoints (gaMorphism G (subwordRootMap G expression j)))
        (coordinateMorphism_points (ULift.up j : ULift.{u} Positions) x)).trans
          (gaMorphism_points G (subwordRootMap G expression j) _))

private def selectedPosition (j : Fin word.length) : Option Positions := by
  classical
  exact if h : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    some ⟨j, h⟩ else none

/-- The ordered selected-root product is a morphism from its affine coordinate space. -/
def subwordProductMorphism (n : ℕ) :
    (affineSpaceVariety K (ULift.{u} Positions)).toOver ⟶ (reductiveVariety G).toOver :=
  ((((List.finRange word.length).take n).filterMap (selectedPosition G expression)).map
    (rootCoordinateMorphism G expression)).prod

/-- The product morphism evaluates to the ordered root product in every prefix. -/
theorem subwordProductMorphism_points (n : ℕ)
    (x : (affineSpaceVariety K (ULift.{u} Positions)).points) :
    mapPoints (subwordProductMorphism G expression n) x =
      reductivePointsEquiv G (subwordRootProduct G expression
        (fun j => affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩) n) := by
  let positions := ((List.finRange word.length).take n).filterMap (selectedPosition G expression)
  change evaluatePoint x ((positions.map (rootCoordinateMorphism G expression)).prod) =
    (reductivePointsMulEquiv G) ((positions.map (fun j =>
      gaParameterPoint (subwordRootMap G expression j)
        (affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩))).prod)
  have hfirst := mapPoints_list_prod
    (X := affineSpaceVariety K (ULift.{u} Positions)) (H := reductiveVariety G)
      (positions.map (rootCoordinateMorphism G expression)) x
  have hlast := (reductivePointsMulEquiv G).toMonoidHom.map_list_prod
    (positions.map (fun j => gaParameterPoint (subwordRootMap G expression j)
      (affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩)))
  exact hfirst.trans ((congrArg List.prod (by
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    exact rootCoordinateMorphism_points G expression j x)).trans hlast.symm)
/-- The root product followed by its signed representative defines a flag morphism. -/
def subwordFlagMorphism (n : ℕ) :
    (affineSpaceVariety K (ULift.{u} Positions)).toOver ⟶ (flagVariety G).toOver :=
  (subwordProductMorphism G expression n *
    constantMorphism (affineSpaceVariety K (ULift.{u} Positions)) (reductiveVariety G)
      (reductivePointsEquiv G (subwordRepresentative G expression n))) ≫ flagQuotientMorphism G

/-- The flag morphism evaluates to the selected root product times its signed representative. -/
theorem subwordFlagMorphism_points (n : ℕ)
    (x : (affineSpaceVariety K (ULift.{u} Positions)).points) :
    mapPoints (subwordFlagMorphism G expression n) x =
      flagVarietyPointsEquiv G (flagProjection G
        (subwordRootProduct G expression
          (fun j => affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩) n *
            subwordRepresentative G expression n)) := by
  let parameters := fun j : Positions =>
    affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩
  have hm := mapPoints_mul (subwordProductMorphism G expression n)
    (constantMorphism (affineSpaceVariety K (ULift.{u} Positions)) (reductiveVariety G)
      (reductivePointsEquiv G (subwordRepresentative G expression n))) x
  have hp := subwordProductMorphism_points G expression n x
  have hc := constantMorphism_points (affineSpaceVariety K (ULift.{u} Positions))
    (reductiveVariety G) (reductivePointsEquiv G (subwordRepresentative G expression n)) x
  have hmul := (reductivePointsMulEquiv G).map_mul
    (subwordRootProduct G expression parameters n) (subwordRepresentative G expression n)
  exact (mapPoints_comp _ (flagQuotientMorphism G) x).trans
    ((congrArg (mapPoints (flagQuotientMorphism G))
      (hm.trans ((congrArg₂ (fun a b => a * b) hp hc).trans hmul.symm))).trans
        (flagQuotientMorphism_points G _))
end SchubertGeometry
