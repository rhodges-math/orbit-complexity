import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionMaps
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons

set_option autoImplicit false

/-! # Cartesian squares for closed-target intersection coordinates

Inverse images commute with the finite intersections in the affine atlas.
Restriction squares are therefore Cartesian, and the affine coordinate
isomorphisms give the same squares for spectra of coordinate rings.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting

namespace SchubertGeometry

universe u

private theorem intersection_preimage_eq {X Y : Scheme.{u}} {I J : Type u}
    (f : X ⟶ Y) (V : I → Y.Opens) (label : J → I)
    (s : {s : Finset J // s.Nonempty}ᵒᵖ) :
    (intersectionOpens (fun j => f ⁻¹ᵁ V (label j))).obj s =
      f ⁻¹ᵁ (intersectionOpens V).obj ((intersectionIndexMap label).op.obj s) := by
  classical
  ext x
  change x ∈ (⨅ j ∈ s.unop.val, f ⁻¹ᵁ V (label j)) ↔
    f x ∈ (⨅ i ∈ s.unop.val.image label, V i)
  rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
  change x ∈ (((s.unop.val.inf (fun j => f ⁻¹ᵁ V (label j))) : X.Opens) : Set X) ↔
    f x ∈ ((((s.unop.val.image label).inf V) : Y.Opens) : Set Y)
  rw [TopologicalSpace.Opens.coe_finset_inf, TopologicalSpace.Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Set.iInf_eq_iInter, Set.mem_iInter]
  constructor
  · intro hx i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hx j hj
  · intro hx j hj
    exact hx (label j) (Finset.mem_image_of_mem label hj)

private theorem restriction_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hle : U ≤ f ⁻¹ᵁ V) (hU : U = f ⁻¹ᵁ V) :
    IsPullback (f.resLE V U hle) U.ι V.ι f := by
  apply IsOpenImmersion.isPullback
  · exact (Scheme.Hom.resLE_comp_ι f hle).symm
  · simpa only [Scheme.Opens.opensRange_ι] using hU.symm

private theorem affine_coordinate_square {K : Type u} [CommRing K]
    {A B C D : Over (Spec (.of K))}
    [IsAffine A.left] [IsAffine B.left] [IsAffine C.left] [IsAffine D.left]
    (f : A ⟶ B) (g : A ⟶ C) (p : B ⟶ D) (q : C ⟶ D)
    (h : IsPullback f.left g.left p.left q.left) :
    IsPullback (((algΓ (.of K)) ⋙ algSpec (.of K)).map f).left
      (((algΓ (.of K)) ⋙ algSpec (.of K)).map g).left
      (((algΓ (.of K)) ⋙ algSpec (.of K)).map p).left
      (((algΓ (.of K)) ⋙ algSpec (.of K)).map q).left := by
  let : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app A) := coordinates_unit_isIso _ A
  let : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app B) := coordinates_unit_isIso _ B
  let : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app C) := coordinates_unit_isIso _ C
  let : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app D) := coordinates_unit_isIso _ D
  exact h.of_iso
    ((Over.forget _).mapIso (asIso ((algΓAlgSpecAdjunction (.of K)).unit.app A)))
    ((Over.forget _).mapIso (asIso ((algΓAlgSpecAdjunction (.of K)).unit.app B)))
    ((Over.forget _).mapIso (asIso ((algΓAlgSpecAdjunction (.of K)).unit.app C)))
    ((Over.forget _).mapIso (asIso ((algΓAlgSpecAdjunction (.of K)).unit.app D)))
    (congrArg (fun k => k.left) ((algΓAlgSpecAdjunction (.of K)).unit.naturality f))
    (congrArg (fun k => k.left) ((algΓAlgSpecAdjunction (.of K)).unit.naturality g))
    (congrArg (fun k => k.left) ((algΓAlgSpecAdjunction (.of K)).unit.naturality p))
    (congrArg (fun k => k.left) ((algΓAlgSpecAdjunction (.of K)).unit.naturality q))

/-- The quotient maps on inverse-image affine intersections have Cartesian
naturality squares on their coordinate spectra. -/
theorem prefix_coordinates_cartesian
    {X Y : Scheme.{u}} {I J K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (V : I → Y.Opens) (label : J → I)
    (hV : ∀ i, IsAffineOpen (V i))
    (hU : ∀ j, IsAffineOpen (f ⁻¹ᵁ V (label j)))
    (s t : {s : Finset J // s.Nonempty}ᵒᵖ) (a : s ⟶ t) :
    let U := fun j => f ⁻¹ᵁ V (label j)
    let B := intersectionCoordinates (f ≫ g) (intersectionOpens U)
    let F := intersectionCoordinates g (intersectionOpens V)
    let H := intersectionIndexMap label
    let β := intersectionCoordinateMap f g U V label (fun _ => le_rfl)
    IsPullback
      (Spec.map (CommRingCat.ofHom (B.map a.unop).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (β.app s.unop).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (β.app t.unop).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (F.map (H.map a.unop)).hom.toRingHom)) := by
  let U := fun j => f ⁻¹ᵁ V (label j)
  let DX := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map (f ≫ g)
  let DY := intersectionOpens V ⋙ Y.restrictFunctor ⋙ Over.map g
  let H := (intersectionIndexMap label).op
  let α := intersectionSchemeMap f g U V label (fun _ => le_rfl)
  have (r : {s : Finset J // s.Nonempty}ᵒᵖ) : IsAffine (DX.obj r).left :=
    intersectionOpens_affine U hU r
  have (r : {s : Finset J // s.Nonempty}ᵒᵖ) : IsAffine ((H ⋙ DY).obj r).left :=
    intersectionOpens_affine V hV (H.obj r)
  have hs : IsPullback (α.app s).left ((intersectionOpens U).obj s).ι
      ((intersectionOpens V).obj (H.obj s)).ι f :=
    restriction_square f _ _ (intersection_preimage_le f U V label (fun _ => le_rfl) s)
      (intersection_preimage_eq f V label s)
  have ht : IsPullback (α.app t).left ((intersectionOpens U).obj t).ι
      ((intersectionOpens V).obj (H.obj t)).ι f :=
    restriction_square f _ _ (intersection_preimage_le f U V label (fun _ => le_rfl) t)
      (intersection_preimage_eq f V label t)
  have hDX : (DX.map a).left ≫ ((intersectionOpens U).obj t).ι =
      ((intersectionOpens U).obj s).ι :=
    (X.restrictFunctor.map ((intersectionOpens U).map a)).w
  have hDY : (DY.map (H.map a)).left ≫ ((intersectionOpens V).obj (H.obj t)).ι =
      ((intersectionOpens V).obj (H.obj s)).ι :=
    (Y.restrictFunctor.map ((intersectionOpens V).map (H.map a))).w
  have hs' : IsPullback (α.app s).left
      ((DX.map a).left ≫ ((intersectionOpens U).obj t).ι)
      ((DY.map (H.map a)).left ≫ ((intersectionOpens V).obj (H.obj t)).ι) f := by
    rw [hDX, hDY]
    exact hs
  have hraw : IsPullback (DX.map a).left (α.app s).left (α.app t).left
      (DY.map (H.map a)).left :=
    (hs'.of_bot (congrArg (fun k => k.left) (α.naturality a)).symm ht).flip
  change IsPullback (((algΓ (.of K)) ⋙ algSpec (.of K)).map (DX.map a)).left
    (((algΓ (.of K)) ⋙ algSpec (.of K)).map (α.app s)).left
    (((algΓ (.of K)) ⋙ algSpec (.of K)).map (α.app t)).left
    (((algΓ (.of K)) ⋙ algSpec (.of K)).map (DY.map (H.map a))).left
  exact affine_coordinate_square (DX.map a) (α.app s) (α.app t)
    (DY.map (H.map a)) hraw

end SchubertGeometry
