import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # quotient maps on closed-target intersection charts -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

private theorem preimage_intersection {X Y : Scheme.{u}} {T : Type u}
    (j : Y ⟶ X) (U : T → X.Opens) (s : {s : Finset T // s.Nonempty}ᵒᵖ) :
    (intersectionOpens (fun t => j ⁻¹ᵁ U t)).obj s =
      j ⁻¹ᵁ (intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj s) := by
  classical
  change (⨅ t ∈ s.unop.val, j ⁻¹ᵁ U t) =
    j ⁻¹ᵁ (⨅ t ∈ s.unop.val.image id, U t)
  simp only [Finset.image_id, ← Finset.inf_eq_iInf]
  exact (map_finset_inf (TopologicalSpace.Opens.comap ⟨j, j.continuous⟩) _ _).symm

/-- Restricting an closed immersion to the inverse images of the same
ambient affine intersections gives surjective coordinate algebra maps. -/
theorem closed_intersection_quotients {X Y : Scheme.{u}} {T K : Type u}
    [CommRing K] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (j : Y ⟶ X) [IsClosedImmersion j] (base : X ⟶ Spec (.of K))
    (U : T → X.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (s : {s : Finset T // s.Nonempty}) :
    Function.Surjective
      (((intersectionCoordinateMap j base (fun t => j ⁻¹ᵁ U t) U id
        (fun _ => le_rfl)).app s).hom) := by
  let V := fun t => j ⁻¹ᵁ U t
  let a := (intersectionSchemeMap j base V U id (fun _ => le_rfl)).app (op s)
  have : IsAffine (((intersectionIndexMap (id : T → T)).op ⋙
      intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map base).obj (op s)).left :=
    intersectionOpens_affine U hU _
  have : IsClosedImmersion a.left := by
    change IsClosedImmersion (j.resLE _ _ _)
    have hclosed (W : X.Opens) (Z : Y.Opens) (h : Z = j ⁻¹ᵁ W) :
        IsClosedImmersion (j.resLE W Z h.le) := by
      subst Z
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      infer_instance
    exact hclosed _ _ (preimage_intersection j U (op s))
  change Function.Surjective a.left.appTop.hom
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine a.left).2


end FrobeniusSplitting
