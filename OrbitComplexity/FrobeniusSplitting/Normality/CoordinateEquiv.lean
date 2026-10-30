import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons

/-! # Coordinate algebras determined by affine scheme isomorphisms -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace FrobeniusSplitting

variable (S : Type u) [CommRing S]

/-- An affine presentation over the base identifies its algebra with the coordinate algebra. -/
def coordinateEquivOfSpecIso (A : CommAlgCat.{u} S) (E : Over (Spec (.of S)))
    [IsAffine E.left] (e : (algSpec (.of S)).obj (.op A) ≅ E) :
    A ≃ₐ[S] ((algΓ (.of S)).obj E).unop := by
  have : IsIso ((algΓAlgSpecAdjunction (.of S)).unit.app E) :=
    coordinates_unit_isIso (.of S) E
  let q := e ≪≫ asIso ((algΓAlgSpecAdjunction (.of S)).unit.app E)
  exact (CommAlgCat.algEquivOfIso
    ((algSpec.fullyFaithful (R := CommRingCat.of S)).preimageIso q).unop).symm

/-- A commuting square of affine presentations gives the same map on coordinate algebras. -/
theorem coordinateEquivOfSpecIso_map (A B : CommAlgCat.{u} S)
    (E F : Over (Spec (.of S))) [IsAffine E.left] [IsAffine F.left]
    (e : (algSpec (.of S)).obj (.op A) ≅ E)
    (d : (algSpec (.of S)).obj (.op B) ≅ F) (f : F ⟶ E) (g : A ⟶ B)
    (h : d.hom ≫ f = (algSpec (.of S)).map g.op ≫ e.hom) (p : A) :
    ((algΓ (.of S)).map f).unop.hom (coordinateEquivOfSpecIso S A E e p) =
      coordinateEquivOfSpecIso S B F d (g.hom p) := by
  have : IsIso ((algΓAlgSpecAdjunction (.of S)).unit.app E) :=
    coordinates_unit_isIso (.of S) E
  have : IsIso ((algΓAlgSpecAdjunction (.of S)).unit.app F) :=
    coordinates_unit_isIso (.of S) F
  let qe := e ≪≫ asIso ((algΓAlgSpecAdjunction (.of S)).unit.app E)
  let qd := d ≪≫ asIso ((algΓAlgSpecAdjunction (.of S)).unit.app F)
  have hu : f ≫ (algΓAlgSpecAdjunction (.of S)).unit.app E =
      (algΓAlgSpecAdjunction (.of S)).unit.app F ≫
        (algSpec (.of S)).map ((algΓ (.of S)).map f) :=
    (algΓAlgSpecAdjunction (.of S)).unit.naturality f
  have hq : qd.hom ≫ (algSpec (.of S)).map ((algΓ (.of S)).map f) =
      (algSpec (.of S)).map g.op ≫ qe.hom := by
    change (d.hom ≫ (algΓAlgSpecAdjunction (.of S)).unit.app F) ≫ _ =
      _ ≫ (e.hom ≫ (algΓAlgSpecAdjunction (.of S)).unit.app E)
    rw [Category.assoc, ← hu, ← Category.assoc, h, Category.assoc]
  have he : ((algSpec.fullyFaithful (R := CommRingCat.of S)).preimageIso qd).hom ≫
      (algΓ (.of S)).map f =
        g.op ≫ ((algSpec.fullyFaithful (R := CommRingCat.of S)).preimageIso qe).hom := by
    apply (algSpec.fullyFaithful (R := CommRingCat.of S)).map_injective
    simpa only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage] using hq
  have hp := congrArg (fun a => a.unop.hom (coordinateEquivOfSpecIso S A E e p)) he
  change (coordinateEquivOfSpecIso S B F d).symm
      (((algΓ (.of S)).map f).unop.hom (coordinateEquivOfSpecIso S A E e p)) =
        g.hom ((coordinateEquivOfSpecIso S A E e).symm
          (coordinateEquivOfSpecIso S A E e p)) at hp
  rw [AlgEquiv.symm_apply_apply] at hp
  apply (coordinateEquivOfSpecIso S B F d).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact hp

end FrobeniusSplitting
