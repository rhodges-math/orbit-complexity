import OrbitComplexity.SchubertGeometry.Normality.Richardson.RichardsonCoordinateKernel
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartQuotients
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The Schubert quotient factors of Richardson coordinates

The ideal identity gives regular quotient maps from both Schubert
coordinate diagrams to the original Richardson coordinate diagram. Their
triangles use the same ambient quotient maps on every intersection.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

universe u

private theorem quotient_factor {K : Type u} [CommRing K]
    {C : Type u} [Category.{u} C]
    {A B M : C ⥤ CommAlgCat.{u} K} (b : A ⟶ B) (m : A ⟶ M)
    (hb : ∀ i, Function.Surjective (b.app i).hom)
    (hker : ∀ i, RingHom.ker (b.app i).hom.toRingHom ≤
      RingHom.ker (m.app i).hom.toRingHom) :
    ∃ θ : B ⟶ M, b ≫ θ = m := by
  let θ₀ (i) := AlgHom.liftOfSurjective (b.app i).hom (hb i) (m.app i).hom (hker i)
  have ht (i) : b.app i ≫ CommAlgCat.ofHom (θ₀ i) = m.app i := by
    apply CommAlgCat.hom_ext
    exact AlgHom.liftOfSurjective_comp (b.app i).hom (hb i) (m.app i).hom (hker i)
  let θ : B ⟶ M :=
    { app := fun i ↦ CommAlgCat.ofHom (θ₀ i)
      naturality := by
        intro i j a
        have : Epi (b.app i) := ConcreteCategory.epi_of_surjective (b.app i) (hb i)
        apply (cancel_epi (b.app i)).mp
        rw [← Category.assoc, ← b.naturality a, Category.assoc, ht,
          ← Category.assoc, ht]
        exact m.naturality a }
  refine ⟨θ, ?_⟩
  apply NatTrans.ext
  exact funext ht

end
end SchubertGeometry

namespace SchubertGeometry

noncomputable section

universe u

/-- Both Schubert coordinate quotients factor through the original
Richardson quotient on the same ambient intersection diagram. -/
theorem richardson_coordinate_factors {K I : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (v w : G.weylGroup)
    (U : I → (flagVariety G).scheme.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    let B := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K kField.toCommRing
      (schubertVariety G w).scheme ((schubertInclusion G w).left ≫ (flagVariety G).toSpec)
      {s : Finset I // s.Nonempty} inferInstance
      (FrobeniusSplitting.intersectionOpens (fun i ↦ (schubertInclusion G w).left ⁻¹ᵁ U i))
    let O := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K kField.toCommRing
      (oppositeSchubertVariety G v).scheme ((oppositeSchubertInclusion G v).left ≫ (flagVariety
        G).toSpec)
      {s : Finset I // s.Nonempty} inferInstance
      (FrobeniusSplitting.intersectionOpens (fun i ↦ (oppositeSchubertInclusion G v).left ⁻¹ᵁ U i))
    let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K kField.toCommRing
      (richardsonVariety G v w).scheme ((richardsonInclusion G v w).left ≫ (flagVariety G).toSpec)
      {s : Finset I // s.Nonempty} inferInstance
      (FrobeniusSplitting.intersectionOpens (fun i ↦ (richardsonInclusion G v w).left ⁻¹ᵁ U i))
    let b := @FrobeniusSplitting.intersectionCoordinateMap.{u}
      (schubertVariety G w).scheme (flagVariety G).scheme I I K kField.toCommRing (schubertInclusion
        G w).left (flagVariety G).toSpec
      (fun i ↦ (schubertInclusion G w).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl)
    let o := @FrobeniusSplitting.intersectionCoordinateMap.{u}
      (oppositeSchubertVariety G v).scheme (flagVariety G).scheme I I K kField.toCommRing
        (oppositeSchubertInclusion G v).left (flagVariety G).toSpec
      (fun i ↦ (oppositeSchubertInclusion G v).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl)
    let m := @FrobeniusSplitting.intersectionCoordinateMap.{u}
      (richardsonVariety G v w).scheme (flagVariety G).scheme I I K kField.toCommRing
        (richardsonInclusion G v w).left (flagVariety G).toSpec
      (fun i ↦ (richardsonInclusion G v w).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl)
    ∃ (θ : B ⟶ M) (ω : O ⟶ M), b ≫ θ = m ∧ o ≫ ω = m := by
  have : IsSeparated (terminal.from (flagVariety G).scheme) := by
    rw [← terminal.comp_from (flagVariety G).toSpec]
    infer_instance
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) := by
    infer_instance
  dsimp only
  obtain ⟨θ, hθ⟩ := SchubertGeometry.quotient_factor
    (@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (schubertVariety G w).scheme (flagVariety G).scheme I I K kField.toCommRing (schubertInclusion
        G w).left (flagVariety G).toSpec
      (fun i ↦ (schubertInclusion G w).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl))
    (@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (richardsonVariety G v w).scheme (flagVariety G).scheme I I K kField.toCommRing
        (richardsonInclusion G v w).left (flagVariety G).toSpec
      (fun i ↦ (richardsonInclusion G v w).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl))
    (fun s ↦ @FrobeniusSplitting.closed_intersection_quotients.{u}
      (flagVariety G).scheme (schubertVariety G w).scheme I K kField.toCommRing inferInstance
      (schubertInclusion G w).left inferInstance (flagVariety G).toSpec U hU s)
    (fun s ↦ (le_sup_left : _ ≤ _ ⊔ _).trans
      (richardson_coordinate_ker G v w U hU s).symm.le)
  obtain ⟨ω, hω⟩ := SchubertGeometry.quotient_factor
    (@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (oppositeSchubertVariety G v).scheme (flagVariety G).scheme I I K kField.toCommRing
        (oppositeSchubertInclusion G v).left (flagVariety G).toSpec
      (fun i ↦ (oppositeSchubertInclusion G v).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl))
    (@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (richardsonVariety G v w).scheme (flagVariety G).scheme I I K kField.toCommRing
        (richardsonInclusion G v w).left (flagVariety G).toSpec
      (fun i ↦ (richardsonInclusion G v w).left ⁻¹ᵁ U i) U id (fun _ ↦ le_rfl))
    (fun s ↦ @FrobeniusSplitting.closed_intersection_quotients.{u}
      (flagVariety G).scheme (oppositeSchubertVariety G v).scheme I K kField.toCommRing
        inferInstance
      (oppositeSchubertInclusion G v).left inferInstance (flagVariety G).toSpec U hU s)
    (fun s ↦ (le_sup_right : _ ≤ _ ⊔ _).trans
      (richardson_coordinate_ker G v w U hU s).symm.le)
  exact ⟨θ, ω, hθ, hω⟩

end
end SchubertGeometry
