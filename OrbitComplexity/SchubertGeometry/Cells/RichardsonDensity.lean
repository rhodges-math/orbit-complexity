import OrbitComplexity.GroupActions.Actions.DenseRestriction
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIntersectionOpen
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIrreducible

/-! # Density of open Richardson strata

The two top-cell loci pull back to dense opens in the reduced Richardson intersection.
Their intersection is the open Richardson stratum. Its preirreducibility therefore passes
to the closed intersection.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
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

private def closureLocus {A X : Scheme.{u}} (i : A ⟶ X) (S : Set X)
    (hS : IsLocallyClosed S) : A.Opens := i ⁻¹ᵁ ambientOpen hS

private theorem closureLocus_mem {A X : Scheme.{u}} (i : A ⟶ X) (S : Set X)
    (hS : IsLocallyClosed S) (hr : Set.range i = closure S) (a : A) :
    a ∈ closureLocus i S hS ↔ i a ∈ S := by
  have hi : i a ∈ closure S := by rw [← hr]; exact ⟨a, rfl⟩
  change i a ∈ ambientOpen hS ↔ i a ∈ S
  constructor
  · intro ha
    rw [ambientOpen_inter hS]
    exact ⟨ha, hi⟩
  · intro ha
    rw [ambientOpen_inter hS] at ha
    exact ha.1

private theorem closureLocus_dense {A X : Scheme.{u}} (i : A ⟶ X) [IsPreimmersion i]
    (S : Set X) (hS : IsLocallyClosed S) (hr : Set.range i = closure S) :
    Dense (closureLocus i S hS : Set A) := by
  have hpre : (closureLocus i S hS : Set A) = i ⁻¹' S := by
    ext a
    exact closureLocus_mem i S hS hr a
  apply i.isEmbedding.isInducing.dense_iff.mpr
  intro a
  rw [hpre, Set.image_preimage_eq_inter_range, hr,
    Set.inter_eq_left.mpr subset_closure]
  rw [← hr]
  exact ⟨a, rfl⟩

private theorem equivariant_points {K : Type u} [Field K]
    (H A X : Variety K) [GrpObj H.toOver] [ModObj H.toOver A.toOver]
    [ModObj H.toOver X.toOver] (i : A.toOver ⟶ X.toOver) [IsModHom H.toOver i]
    (h : H.points) (a : A.points) :
    Variety.mapPoints i (h • a) = h • Variety.mapPoints i a := by
  apply X.pointsEquivOverHom.injective
  change A.pointsEquivOverHom (h • a) ≫ i =
    X.pointsEquivOverHom (h • Variety.mapPoints i a)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul i (H.pointsEquivOverHom h) (A.pointsEquivOverHom a)

private theorem range_preimage {A B C : Type*} (f : A → B) (i : B → C) (g : A → C)
    (hi : Function.Injective i) (hg : ∀ a, i (f a) = g a) :
    Set.range f = i ⁻¹' Set.range g := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (hg a).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, hi ((hg a).trans ha)⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem ordinary_lc (w : G.weylGroup) :
    IsLocallyClosed (Set.range (schubertCellInclusion G w).left) := by
  rw [orbitInclusion_range]
  exact orbitImage_locallyClosed _ _ _

private theorem opposite_lc (w : G.weylGroup) :
    IsLocallyClosed (Set.range (oppositeSchubertCellInclusion G w).left) := by
  rw [orbitInclusion_range]
  exact orbitImage_locallyClosed _ _ _

private def ordinaryLocus (w : G.weylGroup) : (schubertVariety G w).scheme.Opens :=
  closureLocus (A := (schubertVariety G w).scheme) (X := (flagVariety G).scheme)
    (schubertInclusion G w).left (Set.range (schubertCellInclusion G w).left) (ordinary_lc G w)

private def oppositeLocus (w : G.weylGroup) : (oppositeSchubertVariety G w).scheme.Opens :=
  closureLocus (A := (oppositeSchubertVariety G w).scheme) (X := (flagVariety G).scheme)
    (oppositeSchubertInclusion G w).left
      (Set.range (oppositeSchubertCellInclusion G w).left) (opposite_lc G w)

private theorem ordinaryLocus_mem (w : G.weylGroup) (a : (schubertVariety G w).scheme) :
    a ∈ ordinaryLocus G w ↔
      (schubertInclusion G w).left a ∈ Set.range (schubertCellInclusion G w).left :=
  closureLocus_mem (schubertInclusion G w).left _ _ (schubertInclusion_range G w) a

private theorem oppositeLocus_mem (w : G.weylGroup)
    (a : (oppositeSchubertVariety G w).scheme) :
    a ∈ oppositeLocus G w ↔
      (oppositeSchubertInclusion G w).left a ∈
        Set.range (oppositeSchubertCellInclusion G w).left :=
  closureLocus_mem (oppositeSchubertInclusion G w).left _ _
    (oppositeSchubertInclusion_range G w) a

private theorem ordinaryLocus_dense (w : G.weylGroup) :
    Dense (ordinaryLocus G w : Set (schubertVariety G w).scheme) :=
  closureLocus_dense (A := (schubertVariety G w).scheme) (X := (flagVariety G).scheme)
    (schubertInclusion G w).left _ _ (schubertInclusion_range G w)

private theorem oppositeLocus_dense (w : G.weylGroup) :
    Dense (oppositeLocus G w : Set (oppositeSchubertVariety G w).scheme) :=
  closureLocus_dense (A := (oppositeSchubertVariety G w).scheme) (X := (flagVariety G).scheme)
    (oppositeSchubertInclusion G w).left _ _ (oppositeSchubertInclusion_range G w)

private theorem ordinaryLocus_stable (w : G.weylGroup) (h : (borelVariety G).points)
    (a : (schubertVariety G w).points)
    (ha : (schubertVariety G w).pointMap a ∈ ordinaryLocus G w) :
    (schubertVariety G w).pointMap (h • a) ∈ ordinaryLocus G w := by
  apply (ordinaryLocus_mem G w _).mpr
  have hp : Variety.mapPoints (schubertInclusion G w) a ∈
      Set.range (Variety.mapPoints (schubertCellInclusion G w)) := by
    rw [Variety.range_mapPoints]
    exact (ordinaryLocus_mem G w _).mp ha
  have hs := schubertCell_stable G w h hp
  rw [← equivariant_points (borelVariety G) (schubertVariety G w) (flagVariety G)
    (schubertInclusion G w) h a, Variety.range_mapPoints] at hs
  exact hs

private theorem oppositeLocus_stable (w : G.weylGroup)
    (h : (oppositeBorelVariety G).points) (a : (oppositeSchubertVariety G w).points)
    (ha : (oppositeSchubertVariety G w).pointMap a ∈ oppositeLocus G w) :
    (oppositeSchubertVariety G w).pointMap (h • a) ∈ oppositeLocus G w := by
  apply (oppositeLocus_mem G w _).mpr
  have hp : Variety.mapPoints (oppositeSchubertInclusion G w) a ∈
      Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G w)) := by
    rw [Variety.range_mapPoints]
    exact (oppositeLocus_mem G w _).mp ha
  rw [oppositeSchubertCell_points_range] at hp
  have hs := MulAction.mem_orbit_of_mem_orbit h hp
  rw [← oppositeSchubertCell_points_range,
    ← equivariant_points (oppositeBorelVariety G) (oppositeSchubertVariety G w)
      (flagVariety G) (oppositeSchubertInclusion G w) h a, Variety.range_mapPoints] at hs
  exact hs

/-- The open Richardson stratum has dense image in its reduced closed Richardson variety. -/
instance richardsonCellToVariety_dominant (u v : G.weylGroup) :
    IsDominant (richardsonCellToVariety G u v).left := by
  have : Smooth (borelVariety G).toSpec :=
    TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced
      (borelVariety G).toSpec
  have : Smooth (oppositeBorelVariety G).toSpec :=
    TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced
      (oppositeBorelVariety G).toSpec
  let R := richardsonVariety G u v
  let S : Set R.scheme := (richardsonToSchubert G u v).left ⁻¹'
    (ordinaryLocus G v : Set (schubertVariety G v).scheme)
  let T : Set R.scheme := (richardsonToOpposite G u v).left ⁻¹'
    (oppositeLocus G u : Set (oppositeSchubertVariety G u).scheme)
  have hS : Dense S := dense_preimage_of_open_action (borelVariety G)
    (schubertVariety G v) R (richardsonToSchubert G u v) (borelRichardsonFamily_open G u v)
    (ordinaryLocus G v) (ordinaryLocus_dense G v) (ordinaryLocus_stable G v)
  have hT : Dense T := dense_preimage_of_open_action (oppositeBorelVariety G)
    (oppositeSchubertVariety G u) R (richardsonToOpposite G u v)
    (oppositeRichardsonFamily_open G u v) (oppositeLocus G u)
    (oppositeLocus_dense G u) (oppositeLocus_stable G u)
  have hST : Dense (S ∩ T) := hS.inter_of_isOpen_left hT
    ((ordinaryLocus G v).isOpen.preimage (richardsonToSchubert G u v).left.continuous)
  let f₀ : (richardsonCell G u v).scheme ⟶ R.scheme :=
    (richardsonCellToVariety G u v).left
  let i₀ : R.scheme ⟶ (flagVariety G).scheme := (richardsonInclusion G u v).left
  have hrange : Set.range f₀ = S ∩ T := by
    rw [range_preimage f₀ i₀ (richardsonCellInclusion G u v).left i₀.isEmbedding.injective
      (fun q => congrArg (fun m : (richardsonCell G u v).scheme ⟶
        (flagVariety G).scheme => m q)
          (congrArg Over.Hom.left (richardsonCellToVariety_comp G u v)))]
    ext x
    change (i₀ x ∈ Set.range (richardsonCellInclusion G u v).left) ↔ _
    rw [richardsonCellInclusion_range]
    change (_ ∧ _) ↔
      ((richardsonToSchubert G u v).left x ∈ ordinaryLocus G v ∧
        (richardsonToOpposite G u v).left x ∈ oppositeLocus G u)
    rw [ordinaryLocus_mem, oppositeLocus_mem]
    have hleft := congrArg (fun m : R.scheme ⟶ (flagVariety G).scheme => m x)
      (congrArg Over.Hom.left (richardsonToSchubert_comp G u v))
    have hright := congrArg (fun m : R.scheme ⟶ (flagVariety G).scheme => m x)
      (congrArg Over.Hom.left (richardsonToOpposite_comp G u v))
    change (schubertInclusion G v).left ((richardsonToSchubert G u v).left x) = i₀ x at hleft
    change (oppositeSchubertInclusion G u).left ((richardsonToOpposite G u v).left x) =
      i₀ x at hright
    rw [hleft, hright]
  rw [isDominant_iff]
  change Dense (Set.range f₀)
  rwa [hrange]

/-- A reduced closed Richardson intersection is preirreducible, including the empty case. -/
instance richardsonVariety_preirreducible (u v : G.weylGroup) :
    PreirreducibleSpace (richardsonVariety G u v).scheme := by
  let f : (richardsonCell G u v).scheme ⟶ (richardsonVariety G u v).scheme :=
    (richardsonCellToVariety G u v).left
  have hf : IsPreirreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (show IsPreirreducible (Set.univ : Set (richardsonCell G u v).scheme) from
        PreirreducibleSpace.isPreirreducible_univ).image f f.continuous.continuousOn
  constructor
  have hcl := hf.closure
  rwa [f.denseRange.closure_eq] at hcl

end
end SchubertGeometry
