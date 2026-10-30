import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionProjection
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Hopf coordinates of parabolic Levi projections

The group-scheme projection determines a Hopf-algebra map whose retraction is the
coordinate map of the Levi inclusion.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
attribute [local irreducible] parabolicLeviProjection

omit [IsAlgClosed K] [CharZero K] in
private def hopfPullback {A B : _root_.CommHopfAlgCat.{u} K}
    (f : ((hopfSpec (CommRingCat.of K)).obj (Opposite.op A)).X ⟶
      ((hopfSpec (CommRingCat.of K)).obj (Opposite.op B)).X) [IsMonHom f] : B ⟶ A :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimage (Grp.homMk f)).unop

omit [IsAlgClosed K] [CharZero K] in
private theorem hopfPullback_spec {A B : _root_.CommHopfAlgCat.{u} K}
    (f : ((hopfSpec (CommRingCat.of K)).obj (Opposite.op A)).X ⟶
      ((hopfSpec (CommRingCat.of K)).obj (Opposite.op B)).X) [IsMonHom f] :
    ((hopfSpec (CommRingCat.of K)).map (hopfPullback f).op).hom.hom = f := by
  exact congrArg (fun g => g.hom.hom) ((hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage
    (Grp.homMk f))

private abbrev projectionMorphism (I : Set G.rootBase.support) :
    ((hopfSpec (CommRingCat.of K)).obj (Opposite.op (parabolicAlgebra G I).obj)).X ⟶
      ((hopfSpec (CommRingCat.of K)).obj (Opposite.op (G.leviAlgebra I).obj)).X :=
  parabolicLeviProjection G I

private instance projectionMorphism_monoid (I : Set G.rootBase.support) :
    IsMonHom (projectionMorphism G I) := by
  change IsMonHom (parabolicLeviProjection G I)
  infer_instance

/-- The Hopf-algebra pullback of the standard parabolic's Levi projection. -/
def parabolicProjectionMap (I : Set G.rootBase.support) :
    (G.leviAlgebra I).obj ⟶ (parabolicAlgebra G I).obj :=
  hopfPullback (projectionMorphism G I)

/-- The coordinate pullback represents the regular Levi projection. -/
theorem parabolicProjectionMap_spec (I : Set G.rootBase.support) :
    ((hopfSpec (CommRingCat.of K)).map (parabolicProjectionMap G I).op).hom.hom =
      parabolicLeviProjection G I :=
  hopfPullback_spec (projectionMorphism G I)

omit [IsAlgClosed K] [CharZero K] in
private theorem hopf_section {A B : _root_.CommHopfAlgCat.{u} K} (f : A ⟶ B) (g : B ⟶ A)
    (h : ((hopfSpec (CommRingCat.of K)).map g.op).hom.hom ≫
      ((hopfSpec (CommRingCat.of K)).map f.op).hom.hom =
        𝟙 ((hopfSpec (CommRingCat.of K)).obj (Opposite.op A)).X) :
    f ≫ g = 𝟙 A := by
  apply Quiver.Hom.op_inj
  apply (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
  apply Grp.hom_ext
  change ((hopfSpec (CommRingCat.of K)).map (g.op ≫ f.op)).hom.hom =
    ((hopfSpec (CommRingCat.of K)).map (𝟙 (Opposite.op A))).hom.hom
  rw [(hopfSpec (CommRingCat.of K)).map_comp, (hopfSpec (CommRingCat.of K)).map_id,
    Grp.comp_hom_hom, Grp.id_hom_hom]
  exact h

private abbrev pIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (standardParabolicPoints G I)

private theorem parabolic_le_levi (I : Set G.rootBase.support) :
    pIdeal G I ≤ G.leviIdeal I := by
  intro a ha
  apply (HopfIdeal.mem_vanishingIdeal (G.leviPoints I) a).mpr
  intro l
  have hl : l.val ∈ standardParabolicPoints G I := by
    rw [parabolic_eq_levi_sup_unipotent]
    exact (show G.leviPoints I ≤ _ from le_sup_left) l.property
  exact (HopfIdeal.mem_vanishingIdeal (standardParabolicPoints G I) a).mp ha ⟨l.val, hl⟩

private abbrev leviMap (I : Set G.rootBase.support) :
    (parabolicAlgebra G I).obj ⟶ (G.leviAlgebra I).obj :=
  CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj (parabolic_le_levi G I)

private theorem leviMap_spec (I : Set G.rootBase.support) :
    ((hopfSpec (CommRingCat.of K)).map (leviMap G I).op).hom.hom =
      leviParabolicInclusion G I := rfl

private theorem projection_section (I : Set G.rootBase.support) :
    parabolicProjectionMap G I ≫ leviMap G I = 𝟙 (G.leviAlgebra I).obj := by
  apply hopf_section
  exact (congrArg₂ (fun f g => f ≫ g) (leviMap_spec G I)
    (parabolicProjectionMap_spec G I)).trans (parabolicLeviProjection_section G I)

/-- The Levi projection induces an injective Hopf-algebra pullback. -/
theorem parabolicProjectionMap_injective (I : Set G.rootBase.support) :
    Function.Injective (parabolicProjectionMap G I).hom := by
  intro x y hxy
  have h := congrArg (fun a => (leviMap G I).hom a) hxy
  have hs := projection_section G I
  have hx := congrArg (fun f : (G.leviAlgebra I).obj ⟶ (G.leviAlgebra I).obj => f.hom x) hs
  have hy := congrArg (fun f : (G.leviAlgebra I).obj ⟶ (G.leviAlgebra I).obj => f.hom y) hs
  exact hx.symm.trans (h.trans hy)

end SchubertGeometry
