import OrbitComplexity.SchubertGeometry.FlagVariety.Action
import OrbitComplexity.SchubertGeometry.FlagVariety.Proper
import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import Batteries.Tactic.Lint

/-! # Morphisms from flags to group orbits

An orbit map whose base point is fixed by the Borel subgroup descends through the
translated unipotent flag charts. The resulting regular morphism has the expected
formula on group representatives.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section
namespace SchubertGeometry
universe u

private theorem smul_eq_of_inv_mul_mem {A H Y : Type*} [Group A] [Group H]
    [MulAction H Y] (φ : A →* H) (B : Subgroup A) (x : Y)
    (hx : ∀ b ∈ B, φ b • x = x) (g h : A) (hgh : g⁻¹ * h ∈ B) :
    φ g • x = φ h • x := by
  calc
    φ g • x = φ g • (φ (g⁻¹ * h) • x) :=
      congrArg (fun y ↦ φ g • y) (hx _ hgh).symm
    _ = φ h • x := by rw [← mul_smul, ← map_mul, mul_inv_cancel_left]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) (X : GroupActions.Variety K)
  [ModObj (GroupActions.reductiveVariety G).toOver X.toOver]

/-- The orbit map restricted to a translated unipotent flag chart. -/
def flagOrbitChart (x : X.points) (g : G.points) :
    (GroupActions.oppositeUnipotentVariety G).toOver ⟶ X.toOver :=
  flagChartMap G g ≫ GroupActions.Variety.orbitMorphism (GroupActions.reductiveVariety G) X x

/-- The orbit chart sends a unipotent coordinate to its group representative acting on the point. -/
theorem flagOrbitChart_points (x : X.points) (g : G.points)
    (u : (GroupActions.oppositeUnipotentVariety G).points) :
    GroupActions.Variety.mapPoints (flagOrbitChart G X x g) u =
      GroupActions.reductivePointsMulEquiv G
        (g * (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points)) • x := by
  simp only [flagOrbitChart, GroupActions.Variety.mapPoints_comp,
    GroupActions.Variety.mapPoints_orbitMorphism, flagChartMap_points]
  rfl

variable (x : X.points)

private theorem orbitChart_compatible
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) (g h : G.points) :
    flagOverlapInclusion G g h ≫ flagOrbitChart G X x g =
      (flagTransition G g h ≫ flagOverlapInclusion G h g) ≫ flagOrbitChart G X x h := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  simp only [GroupActions.Variety.mapPoints_comp, flagOrbitChart_points]
  apply smul_eq_of_inv_mul_mem (GroupActions.reductivePointsMulEquiv G).toMonoidHom
    G.borelPoints x hx
  apply (flagProjection_eq_iff G _ _).mp
  exact (flagTransition_flag G g h p).symm

private theorem orbitCondition
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x)
    (ij : G.points × G.points) :
    (flagGlueData G).toGlueData.diagram.fst ij ≫ (flagOrbitChart G X x ij.1).left =
      (flagGlueData G).toGlueData.diagram.snd ij ≫ (flagOrbitChart G X x ij.2).left := by
  change (flagOverlapInclusion G ij.1 ij.2).left ≫ (flagOrbitChart G X x ij.1).left =
    ((flagTransition G ij.1 ij.2).left ≫ (flagOverlapInclusion G ij.2 ij.1).left) ≫
      (flagOrbitChart G X x ij.2).left
  exact congrArg Over.Hom.left (orbitChart_compatible G X x hx ij.1 ij.2)

private def orbitSchemeHom
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) :
    flagScheme G ⟶ X.scheme :=
  Multicoequalizer.desc (flagGlueData G).toGlueData.diagram X.scheme
    (fun g ↦ (flagOrbitChart G X x g).left) (orbitCondition G X x hx)

private theorem orbitSchemeHom_chart
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) (g : G.points) :
    flagSchemeChart G g ≫ orbitSchemeHom G X x hx = (flagOrbitChart G X x g).left := by
  exact Multicoequalizer.π_desc (flagGlueData G).toGlueData.diagram X.scheme
    (fun g ↦ (flagOrbitChart G X x g).left) (orbitCondition G X x hx) g

private theorem orbitSchemeHom_toSpec
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) :
    orbitSchemeHom G X x hx ≫ X.toSpec = flagSchemeToSpec G := by
  apply (flagSchemeCover G).hom_ext
  intro g
  change G.points at g
  change flagSchemeChart G g ≫ (orbitSchemeHom G X x hx ≫ X.toSpec) =
    flagSchemeChart G g ≫ flagSchemeToSpec G
  rw [← Category.assoc, orbitSchemeHom_chart, flagSchemeChart_toSpec]
  exact (flagOrbitChart G X x g).w

/-- A group orbit map descends regularly to flags when the Borel fixes its base point. -/
def flagOrbitMorphism
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) :
    (flagVariety G).toOver ⟶ X.toOver :=
  Over.homMk (orbitSchemeHom G X x hx) (orbitSchemeHom_toSpec G X x hx)

/-- The descended morphism restricts to the orbit map on every translated unipotent chart. -/
theorem flagOrbitMorphism_chart
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) (g : G.points) :
    flagChartMorphism G g ≫ flagOrbitMorphism G X x hx = flagOrbitChart G X x g := by
  apply Over.OverMorphism.ext
  exact orbitSchemeHom_chart G X x hx g


/-- The descended orbit morphism sends a flag representative to its action on the base point. -/
theorem flagOrbitMorphism_representative
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x)
    (g : G.points) :
    GroupActions.Variety.mapPoints (flagOrbitMorphism G X x hx)
      (flagVarietyPointsEquiv G (flagProjection G g)) =
        GroupActions.reductivePointsMulEquiv G g • x := by
  have h := congrArg (fun f :
      (GroupActions.oppositeUnipotentVariety G).toOver ⟶ X.toOver ↦
        GroupActions.Variety.mapPoints f 1) (flagOrbitMorphism_chart G X x hx g)
  simp only [GroupActions.Variety.mapPoints_comp, flagChartMorphism_points,
    flagOrbitChart_points, flagChartPoint, map_one, OneMemClass.coe_one, mul_one] at h
  exact h

/-- The descended orbit morphism is equivariant for the reductive group. -/
instance flagOrbitMorphism_isModHom
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) :
    IsModHom (GroupActions.reductiveVariety G).toOver (flagOrbitMorphism G X x hx) := by
  apply GroupActions.Variety.isModHom_of_points (GroupActions.reductiveVariety G)
    (flagVariety G) X
  intro h p
  obtain ⟨g, rfl⟩ := (GroupActions.reductivePointsMulEquiv G).surjective h
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective p
  obtain ⟨a, rfl⟩ := flagProjection_surjective G q
  rw [flagVarietyAction_points, ← flagProjection_smul,
    flagOrbitMorphism_representative, flagOrbitMorphism_representative, map_mul, mul_smul]

/-- Exact Borel stabilizers give injective orbit morphisms on rational points. -/
theorem flagOrbitMorphism_injective
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x)
    (hstab : ∀ g : G.points,
      GroupActions.reductivePointsMulEquiv G g • x = x → g ∈ G.borelPoints) :
    Function.Injective (GroupActions.Variety.mapPoints (flagOrbitMorphism G X x hx)) := by
  intro p q hpq
  obtain ⟨a, rfl⟩ := (flagVarietyPointsEquiv G).surjective p
  obtain ⟨g, rfl⟩ := flagProjection_surjective G a
  obtain ⟨b, rfl⟩ := (flagVarietyPointsEquiv G).surjective q
  obtain ⟨h, rfl⟩ := flagProjection_surjective G b
  rw [flagOrbitMorphism_representative, flagOrbitMorphism_representative] at hpq
  apply congrArg (flagVarietyPointsEquiv G)
  apply (flagProjection_eq_iff G g h).mpr
  apply hstab
  rw [map_mul, map_inv, mul_smul, ← hpq, inv_smul_smul]

private theorem proper_over {S : Scheme.{u}} (A B : Over S)
    [IsProper A.hom] [IsSeparated B.hom] (f : A ⟶ B) : IsProper f.left := by
  have : IsProper (f.left ≫ B.hom) := f.w.symm ▸ inferInstance
  exact IsProper.of_comp f.left B.hom

/-- Every descended flag orbit morphism is proper. -/
instance flagOrbitMorphism_isProper
    (hx : ∀ b ∈ G.borelPoints, GroupActions.reductivePointsMulEquiv G b • x = x) :
    IsProper (flagOrbitMorphism G X x hx).left :=
  @proper_over.{u} (Spec (CommRingCat.of K)) (flagVariety G).toOver X.toOver
    (flagVariety_isProper G) X.separated (flagOrbitMorphism G X x hx)

end SchubertGeometry
