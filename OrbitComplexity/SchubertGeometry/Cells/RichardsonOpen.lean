import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Open Richardson strata in their closed varieties

Each cell is open in its closure. Intersecting the two ambient open loci identifies the reduced
open Richardson stratum with an open subvariety of the closed Richardson variety.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace GroupActions ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u

private theorem ambient_exists {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsLocallyClosed S) : ∃ U : Set X, IsOpen U ∧ S = U ∩ closure S :=
  ((isLocallyClosed_tfae S).out 1 5).mp hS

private def ambientOpen {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsLocallyClosed S) : Opens X :=
  ⟨Classical.choose (ambient_exists hS), (Classical.choose_spec (ambient_exists hS)).1⟩

private theorem ambientOpen_inter {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsLocallyClosed S) : S = (ambientOpen hS : Set X) ∩ closure S :=
  (Classical.choose_spec (ambient_exists hS)).2

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem cell_locallyClosed (w : G.weylGroup) :
    IsLocallyClosed (Set.range (schubertCellInclusion G w).left) := by
  rw [GroupActions.orbitInclusion_range]
  exact orbitImage_locallyClosed _ _ _

private theorem opposite_locallyClosed (w : G.weylGroup) :
    IsLocallyClosed (Set.range (oppositeSchubertCellInclusion G w).left) := by
  rw [GroupActions.orbitInclusion_range]
  exact orbitImage_locallyClosed _ _ _

private def intersectionOpen (u v : G.weylGroup) : (flagVariety G).scheme.Opens :=
  ambientOpen (cell_locallyClosed G v) ⊓ ambientOpen (opposite_locallyClosed G u)

private def richardsonOpen (u v : G.weylGroup) : (richardsonVariety G u v).scheme.Opens :=
  (richardsonInclusion G u v).left ⁻¹ᵁ intersectionOpen G u v

private def openSource (u v : G.weylGroup) : Variety K :=
  (richardsonVariety G u v).openSubvariety (richardsonOpen G u v)

private def openFlagMap (u v : G.weylGroup) :
    (openSource G u v).toOver ⟶ (flagVariety G).toOver :=
  (richardsonVariety G u v).openInclusion (richardsonOpen G u v) ≫
    richardsonInclusion G u v

private theorem openFlagMap_range (u v : G.weylGroup) :
    Set.range (openFlagMap G u v).left = Set.range (richardsonCellInclusion G u v).left := by
  let r₀ : (richardsonVariety G u v).scheme ⟶ (flagVariety G).scheme :=
    (richardsonInclusion G u v).left
  change Set.range (r₀ ∘
    ((richardsonVariety G u v).openInclusion (richardsonOpen G u v)).left) = _
  rw [Set.range_comp, Variety.openInclusion_range]
  change r₀ '' (r₀ ⁻¹' (intersectionOpen G u v : Set (flagVariety G).scheme)) = _
  rw [Set.image_preimage_eq_inter_range, richardsonInclusion_range,
    schubertInclusion_range, oppositeSchubertInclusion_range, richardsonCellInclusion_range]
  change ((ambientOpen (cell_locallyClosed G v) : Set _) ∩
      (ambientOpen (opposite_locallyClosed G u) : Set _)) ∩
    (closure (Set.range (schubertCellInclusion G v).left) ∩
      closure (Set.range (oppositeSchubertCellInclusion G u).left)) = _
  exact (Set.inter_inter_inter_comm _ _ _ _).trans
    (congrArg₂ (fun S T : Set (flagVariety G).scheme => S ∩ T)
      (ambientOpen_inter (cell_locallyClosed G v)).symm
      (ambientOpen_inter (opposite_locallyClosed G u)).symm)

private theorem openFlagMap_points (u v : G.weylGroup) :
    Set.range (Variety.mapPoints (richardsonCellInclusion G u v)) =
      Set.range (Variety.mapPoints (openFlagMap G u v)) := by
  rw [Variety.range_mapPoints, Variety.range_mapPoints, openFlagMap_range]

private instance openFlagMap_preimmersion (u v : G.weylGroup) :
    IsPreimmersion (openFlagMap G u v).left :=
  inferInstanceAs (IsPreimmersion
    (((richardsonVariety G u v).openInclusion (richardsonOpen G u v)).left ≫
      (richardsonInclusion G u v).left))

private def openIso (u v : G.weylGroup) :
    (richardsonCell G u v).toOver ≅ (openSource G u v).toOver :=
  Variety.pointImageIso (richardsonCellInclusion G u v) (openFlagMap G u v)
    (openFlagMap_points G u v)

/-- The open Richardson stratum maps regularly into its closed Richardson variety. -/
def richardsonCellToVariety (u v : G.weylGroup) :
    (richardsonCell G u v).toOver ⟶ (richardsonVariety G u v).toOver :=
  (openIso G u v).hom ≫
    (richardsonVariety G u v).openInclusion (richardsonOpen G u v)

/-- The open Richardson map commutes with the two inclusions into the flag variety. -/
@[reassoc]
theorem richardsonCellToVariety_comp (u v : G.weylGroup) :
    richardsonCellToVariety G u v ≫ richardsonInclusion G u v =
      richardsonCellInclusion G u v := by
  change ((openIso G u v).hom ≫
    (richardsonVariety G u v).openInclusion (richardsonOpen G u v)) ≫ _ = _
  exact (Category.assoc (openIso G u v).hom
    ((richardsonVariety G u v).openInclusion (richardsonOpen G u v))
    (richardsonInclusion G u v)).trans
      (Variety.pointImageIso_hom_comp _ _ (openFlagMap_points G u v))

attribute [local irreducible] richardsonCellToVariety

/-- The open Richardson stratum includes by an open immersion into its closed variety. -/
instance richardsonCellToVariety_isOpen (u v : G.weylGroup) :
    IsOpenImmersion (richardsonCellToVariety G u v).left := by
  let p : (openSource G u v).scheme ⟶ (richardsonVariety G u v).scheme :=
    ((richardsonVariety G u v).openInclusion (richardsonOpen G u v)).left
  have : IsOpenImmersion p := Variety.openInclusion_isOpenImmersion _ _
  have : IsIso (openIso G u v).hom.left :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (openIso G u v)).hom))
  exact inferInstanceAs (IsOpenImmersion ((openIso G u v).hom.left ≫ p))

private theorem equivariant_of_comp {C : Type*} [Category C]
    [CartesianMonoidalCategory C] (H X Y Z : C) [MonObj H]
    [ModObj H X] [ModObj H Y] [ModObj H Z]
    (f : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z) [Mono i]
    [IsModHom H i] [IsModHom H j] (h : f ≫ i = j) : IsModHom H f := by
  constructor
  apply (cancel_mono i).mp
  rw [Category.assoc, h, IsModHom.smul_hom]
  rw [Category.assoc, IsModHom.smul_hom, ← Category.assoc,
    ← MonoidalCategory.MonoidalLeftAction.actionHomRight_comp, h]

/-- The open Richardson immersion respects the ordinary torus actions. -/
instance richardsonCellToVariety_torus (u v : G.weylGroup) :
    IsModHom (torusVariety G).toOver (richardsonCellToVariety G u v) := by
  have : Mono (richardsonInclusion G u v) := Over.mono_of_mono_left _
  exact equivariant_of_comp (torusVariety G).toOver _ _ _
    (richardsonCellToVariety G u v) (richardsonInclusion G u v)
    (richardsonCellInclusion G u v) (richardsonCellToVariety_comp G u v)

end
end SchubertGeometry
