import OrbitComplexity.SchubertGeometry.FlagVariety.OppositeConjugation
import OrbitComplexity.SchubertGeometry.Cells.OppositeTranslation
import OrbitComplexity.SchubertGeometry.BSDH.Actions
import OrbitComplexity.SchubertGeometry.BSDH.ConnectedFibres
import OrbitComplexity.SchubertGeometry.Cells.OppositeActions

/-! # Opposite BSDH endpoints

Conjugation transports the Borel action to the opposite Borel. Longest flag
translation then transports the reduced endpoint and its proper connected fibres.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u v w

private theorem equivariant_of_comp {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (H X Y Z : C) [MonObj H]
    [ModObj H X] [ModObj H Y] [ModObj H Z]
    (f : X ⟶ Y) (j : Y ⟶ Z) [Mono j] [IsModHom H j] [IsModHom H (f ≫ j)] :
    IsModHom H f := by
  constructor
  apply (cancel_mono j).mp
  calc
    (γ[H, X] ≫ f) ≫ j = γ[H, X] ≫ (f ≫ j) := Category.assoc _ _ _
    _ = (H ◁ (f ≫ j)) ≫ γ[H, Z] := IsModHom.smul_hom
    _ = ((H ◁ f) ≫ γ[H, Y]) ≫ j := by
      simp only [whiskerLeft_comp, Category.assoc, IsModHom.smul_hom]
      rfl

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem oppositeConjugation_points (o : (oppositeBorelVariety G).points) :
    (borelPointsMulEquiv G
      (Variety.mapPoints (oppositeBorelConjugationIso G).inv o) : G.points) =
        G.longestPoint⁻¹ * (oppositeBorelPointsMulEquiv G o : G.points) *
          G.longestPoint := by
  have hc : (oppositeBorelConjugationIso G).inv ≫ borelInclusion G ≫
      (reductiveConjugation G G.longestPoint).hom = oppositeBorelInclusion G := by
    rw [← oppositeBorelConjugation_comp, Iso.inv_hom_id_assoc]
  have hp := congrArg (fun f => Variety.mapPoints f o) hc
  rw [Variety.mapPoints_comp, Variety.mapPoints_comp, borelInclusion_points,
    reductiveConjugation_points, oppositeBorelInclusion_points] at hp
  have he := (reductivePointsEquiv G).injective hp
  calc
    _ = G.longestPoint⁻¹ *
        (G.longestPoint * (borelPointsMulEquiv G
          (Variety.mapPoints (oppositeBorelConjugationIso G).inv o) : G.points) *
            G.longestPoint⁻¹) * G.longestPoint := by group
    _ = _ := by rw [he]

private theorem translated_flag_smul (o : (oppositeBorelVariety G).points)
    (z : (flagVariety G).points) :
    Variety.mapPoints (longestFlagIso G).hom
        (Variety.mapPoints (oppositeBorelConjugationIso G).inv o • z) =
      o • Variety.mapPoints (longestFlagIso G).hom z := by
  change Variety.mapPoints (Variety.translateMorphism (reductiveVariety G)
      (flagVariety G) (reductivePointsMulEquiv G G.longestPoint)) _ =
    o • Variety.mapPoints (Variety.translateMorphism (reductiveVariety G)
      (flagVariety G) (reductivePointsMulEquiv G G.longestPoint)) z
  rw [Variety.mapPoints_translateMorphism, Variety.mapPoints_translateMorphism]
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective z
  simp only [borelFlag_smul, flagVarietyAction_points, oppositeBorelFlag_smul,
    oppositeConjugation_points, ← mul_smul]
  congr 1
  group

omit [IsAlgClosed K] [CharZero K] in
private theorem points_map_smul (H X Y : Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f = _
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul,
    IsModHom.map_smul]
  rfl

/-- The opposite Borel acts on the ordinary BSDH source by conjugation. -/
@[instance_reducible] def bsdhOppositeAction (word : List G.rootBase.support) :
    ModObj (oppositeBorelVariety G).toOver (bsdhVariety G word).toOver := by
  let := bsdhBorelAction G word
  exact Mod.scalarRestriction (oppositeBorelConjugationIso G).inv
    (bsdhVariety G word).toOver

/-- The opposite endpoint is the ordinary endpoint followed by longest translation. -/
def bsdhOppositeEndpoint (word : List G.rootBase.support) :
    (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver :=
  (Over.homMk (bsdhMap G word) rfl :
    (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver) ≫ (longestFlagIso G).hom

/-- The translated endpoint is equivariant for the opposite action. -/
theorem bsdhOppositeEquivariant (word : List G.rootBase.support) :
    letI := bsdhOppositeAction G word
    IsModHom (oppositeBorelVariety G).toOver (bsdhOppositeEndpoint G word) := by
  let := bsdhBorelAction G word
  have := bsdhBorelEquivariant G word
  let := bsdhOppositeAction G word
  apply Variety.isModHom_of_points (oppositeBorelVariety G) (bsdhVariety G word)
    (flagVariety G)
  intro o x
  rw [Variety.restricted_smul (oppositeBorelConjugationIso G).inv]
  simp only [bsdhOppositeEndpoint, Variety.mapPoints_comp, points_map_smul]
  exact translated_flag_smul G o _

/-- The reduced translated endpoint factors through the opposite Schubert variety. -/
def bsdhOppositeSchubertMap (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    (bsdhVariety G word).toOver ⟶
      (oppositeSchubertVariety G (G.longestElement * simpleWeylWord G.rootBase word)).toOver :=
  bsdhSchubertMap G word hred ≫
    (oppositeSchubertIso G (simpleWeylWord G.rootBase word)).hom

/-- The opposite Schubert factor retains the translated flag endpoint. -/
theorem bsdhOppositeSchubertMap_comp (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    bsdhOppositeSchubertMap G word hred ≫
        oppositeSchubertInclusion G (G.longestElement * simpleWeylWord G.rootBase word) =
      bsdhOppositeEndpoint G word := by
  rw [bsdhOppositeSchubertMap, Category.assoc, oppositeSchubertIso_comp,
    ← Category.assoc]
  apply congrArg (fun f => f ≫ (longestFlagIso G).hom)
  apply Over.OverMorphism.ext
  exact bsdhSchubertMap_comp G word hred

/-- The proper opposite Schubert endpoint is opposite Borel equivariant. -/
theorem bsdhOppositeSchubertMap_equivariant (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    letI := bsdhOppositeAction G word
    IsModHom (oppositeBorelVariety G).toOver (bsdhOppositeSchubertMap G word hred) := by
  let := bsdhOppositeAction G word
  have : IsModHom (oppositeBorelVariety G).toOver
      (bsdhOppositeSchubertMap G word hred ≫ oppositeSchubertInclusion G
        (G.longestElement * simpleWeylWord G.rootBase word)) := by
    rw [bsdhOppositeSchubertMap_comp]
    exact bsdhOppositeEquivariant G word
  have : Mono (oppositeSchubertInclusion G
      (G.longestElement * simpleWeylWord G.rootBase word)) := Over.mono_of_mono_left _
  exact equivariant_of_comp _ _ _ _ _
    (oppositeSchubertInclusion G (G.longestElement * simpleWeylWord G.rootBase word))

/-- Properness is preserved by the opposite Schubert target isomorphism. -/
instance bsdhOppositeSchubertMap_isProper (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    IsProper (bsdhOppositeSchubertMap G word hred).left := by
  change IsProper ((bsdhSchubertMap G word hred).left ≫
    (oppositeSchubertIso G (simpleWeylWord G.rootBase word)).hom.left)
  infer_instance

/-- The opposite Schubert endpoint has geometrically connected fibres. -/
theorem bsdhOppositeSchubert_geomConnected (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    GeometricallyConnected (bsdhOppositeSchubertMap G word hred).left := by
  have : GeometricallyConnected (bsdhSchubertMap G word hred).left :=
    bsdhSchubert_geomConnected G word hred
  change GeometricallyConnected ((bsdhSchubertMap G word hred).left ≫
    (oppositeSchubertIso G (simpleWeylWord G.rootBase word)).hom.left)
  exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
    (bsdhSchubertMap G word hred).left
      (oppositeSchubertIso G (simpleWeylWord G.rootBase word)).hom.left).mpr inferInstance

end
end SchubertGeometry
