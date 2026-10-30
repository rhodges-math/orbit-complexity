import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones

/-! # Coordinate comparison for the retained refinement domains

The original affine chart is related to the singleton node of the global source
diagram by the specified open-image isomorphism. The comparison retains the
spectrum-to-source leg, not only an abstract coordinate-ring isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

universe u

private theorem inverse_unit_naturality (K : CommRingCat.{u})
    {A B : Over (Spec K)} [IsAffine A.left] [IsAffine B.left] (e : A ≅ B) :
    letI := coordinates_unit_isIso K A
    letI := coordinates_unit_isIso K B
    (algSpec K).map ((algΓ K).map e.inv) ≫
        inv ((algΓAlgSpecAdjunction K).unit.app A) =
      inv ((algΓAlgSpecAdjunction K).unit.app B) ≫ e.inv := by
  let : IsIso ((algΓAlgSpecAdjunction K).unit.app A) := coordinates_unit_isIso K A
  let : IsIso ((algΓAlgSpecAdjunction K).unit.app B) := coordinates_unit_isIso K B
  have hn : e.inv ≫ (algΓAlgSpecAdjunction K).unit.app A =
      (algΓAlgSpecAdjunction K).unit.app B ≫ (algSpec K).map ((algΓ K).map e.inv) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (algΓAlgSpecAdjunction K).unit.naturality e.inv
  apply (cancel_mono ((algΓAlgSpecAdjunction K).unit.app A)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
    hn, IsIso.inv_hom_id_assoc]

/-- The singleton coordinates of a specified global affine source cover agree
with its retained original chart coordinates through the chart isomorphism.
The spectrum comparison preserves the full original chart leg. -/
theorem refinement_chart_coordinates {K I : Type u} [kComm : CommRing K]
    (X : Over (Spec (.of K)))
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (U : I → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) (i : I)
    (Z : Over (Spec (.of K))) [IsAffine Z.left] (l : Z ⟶ X)
    (eZ : Z.left ≅ (U i).toScheme) (hleg : eZ.hom ≫ (U i).ι = l.left) :
    letI := coordinates_unit_isIso (.of K) Z
    let s : {s : Finset I // s.Nonempty} := ⟨{i}, Finset.singleton_nonempty i⟩
    ∃ e : (@intersectionCoordinates.{u,u,u} K kComm X.left X.hom
        {s : Finset I // s.Nonempty} (inferInstanceAs (Category {s : Finset I // s.Nonempty}))
        (intersectionOpens U)).obj s ≃ₐ[K] ((algΓ (.of K)).obj Z).unop,
      (algSpec (.of K)).map (CommAlgCat.ofHom e.toAlgHom).op ≫
          (intersectionCoordinateCocone X.hom U hU).ι.app (.op s) =
        inv ((algΓAlgSpecAdjunction (.of K)).unit.app Z) ≫ l := by
  classical
  let s : {s : Finset I // s.Nonempty} := ⟨{i}, Finset.singleton_nonempty i⟩
  let D := intersectionOpens U ⋙ X.left.restrictFunctor ⋙ Over.map X.hom
  let (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (D.obj s).left :=
    intersectionOpens_affine U hU s
  have hs : (intersectionOpens U).obj (.op s) = U i := by
    simp [intersectionOpens, s]
  let A := D.obj (.op s)
  let : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app A) :=
    coordinates_unit_isIso (.of K) A
  let : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app Z) :=
    coordinates_unit_isIso (.of K) Z
  let B := Over.mk ((U i).ι ≫ X.hom)
  let single : A ≅ B := Over.isoMk (X.left.isoOfEq hs) (by
    change (X.left.isoOfEq hs).hom ≫ ((U i).ι ≫ X.hom) = _
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
    rfl)
  let original : Z ≅ B := Over.isoMk eZ (by
    change eZ.hom ≫ ((U i).ι ≫ X.hom) = Z.hom
    rw [← Category.assoc, hleg]
    exact l.w)
  let E : A ≅ Z := single ≪≫ original.symm
  let e := CommAlgCat.algEquivOfIso (((algΓ (.of K)).mapIso E).unop.symm)
  let inc : A ⟶ X := Over.homMk ((intersectionOpens U).obj (.op s)).ι rfl
  have hinc : E.inv ≫ inc = l := by
    apply Over.OverMorphism.ext
    change (eZ.hom ≫ (X.left.isoOfEq hs).inv) ≫
      ((intersectionOpens U).obj (.op s)).ι = l.left
    rw [Category.assoc, Scheme.isoOfEq_inv_ι, hleg]
  refine ⟨e, ?_⟩
  change (algSpec (.of K)).map ((algΓ (.of K)).map E.inv) ≫
      (inv ((algΓAlgSpecAdjunction (.of K)).unit.app A) ≫ inc) = _
  rw [← Category.assoc, inverse_unit_naturality]
  rw [Category.assoc, hinc]

end
end SchubertGeometry
