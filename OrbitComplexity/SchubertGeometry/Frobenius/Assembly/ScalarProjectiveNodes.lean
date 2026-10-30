import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveTransitions
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import OrbitComplexity.FrobeniusSplitting.Normality.AffinePushouts
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Projective nodes on a prescribed scalar append model

Tensor coefficients and projective base change construct the full projective
nodes on the given scalar model. Each node retains its old and scalar-base
projections, and the original cocone cover supplies a cover after extension.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private projective_pullback from
    OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
open private affineProjectiveMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveTransitions

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A (ULift.{u} (Fin 2))

private abbrev coefficient (S T A : Type u) [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] : line (T ⊗[S] A) ⟶ line A :=
  projectiveCoeffMap (ULift.{u} (Fin 2))
    (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom

private abbrev nodeBase (S T A : Type u) [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] : line (T ⊗[S] A) ⟶ Spec (.of T) :=
  projectiveToSpec (T ⊗[S] A) (ULift.{u} (Fin 2)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[S] A)))

private theorem projectiveScalar_square (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A] [Algebra S T] [Algebra S A] :
    IsPullback (coefficient S T A) (nodeBase S T A)
      (projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
  have hT := ((isPushout_iff_spec_pullback _ _ _ _).mp
    (CommRingCat.isPushout_tensorProduct S T A)).flip
  exact (projective_pullback (ULift.{u} (Fin 2))
    (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom).paste_vert hT

private theorem scalar_node (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A] [Algebra S T] [Algebra S A]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of S)) (baseT : Y ⟶ Spec (.of T))
    (q : Y ⟶ X)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (k : line A ⟶ X) [IsOpenImmersion k]
    (hbase : k ≫ base = projectiveToSpec A (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S A))) :
    ∃ K : line (T ⊗[S] A) ⟶ Y,
      K ≫ q = coefficient S T A ≫ k ∧ K ≫ baseT = nodeBase S T A ∧
        IsPullback (coefficient S T A) K k q ∧ IsOpenImmersion K := by
  have houter : IsPullback (coefficient S T A) (nodeBase S T A) (k ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    simpa only [hbase] using projectiveScalar_square S T A
  let K := hq.lift (coefficient S T A ≫ k) (nodeBase S T A)
    (by rw [Category.assoc, houter.w])
  have hK : IsPullback (coefficient S T A) K k q := houter.of_bot' hq
  refine ⟨K, hq.lift_fst _ _ _, hq.lift_snd _ _ _, hK, ?_⟩
  exact MorphismProperty.of_isPullback hK inferInstance

/-- Full projective nodes on the given scalar model, with both projections,
their Cartesian comparisons, their cover, and their affine transitions. -/
def scalarProjectiveNodeData {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {J : Type u} [Category J] (N : J ⥤ CommAlgCat.{u} S)
    (D : Jᵒᵖ ⥤ Scheme.{u}) (E : ∀ s, D.obj (.op s) ≅ line (N.obj s))
    (c : Cocone D) {Y : Scheme.{u}} (baseT : Y ⟶ Spec (.of T)) (q : Y ⟶ c.pt) : Prop :=
  let M := fixedFibreDiagram (R := T) (M := T) N
  let μ := fixedScalarMap S T N
  ∃ K : ∀ s, line (T ⊗[S] N.obj s) ⟶ Y,
    (∀ s, K s ≫ q = coefficient S T (N.obj s) ≫ (E s).inv ≫ c.ι.app (.op s)) ∧
    (∀ s, K s ≫ baseT = nodeBase S T (N.obj s)) ∧
    (∀ s, IsPullback (coefficient S T (N.obj s)) (K s)
      ((E s).inv ≫ c.ι.app (.op s)) q) ∧
    ∃ hOpen : ∀ s, IsOpenImmersion (K s),
    let : ∀ s, IsOpenImmersion (K s) := hOpen
    (⨆ s, (K s).opensRange) = ⊤ ∧
    ∀ {s t : J} (f : s ⟶ t) (a : (N.obj t)ˣ) (b : N.obj t),
      D.map f.op ≫ (E s).hom = (E t).hom ≫ affineProjectiveMap (N.map f).hom.toRingHom a b →
      affineProjectiveMap (M.map f).hom.toRingHom
        (Units.map (μ.app t).hom.toMonoidHom a) ((μ.app t).hom b) ≫ K s = K t

/-- The original projective append cocone constructs its full covering nodes
on the prescribed scalar target, retaining every affine cocone transition. -/
theorem exists_scalar_projective_nodes {S T : Type u}
    [CommRing S] [CommRing T] [Algebra S T] {J : Type u} [Category J]
    (N : J ⥤ CommAlgCat.{u} S) (D : Jᵒᵖ ⥤ Scheme.{u})
    (E : ∀ s, D.obj (.op s) ≅ line (N.obj s)) (c : Cocone D)
    (hopen : ∀ s, IsOpenImmersion (c.ι.app (.op s)))
    (hcover : ∀ (Z : Scheme.{u}) (f : Z ⟶ c.pt) (y : Z),
      ∃ s, ∃ z : (pullback f (c.ι.app (.op s)) : Scheme.{u}),
        (pullback.fst f (c.ι.app (.op s))) z = y)
    (base : c.pt ⟶ Spec (.of S))
    (hbase : ∀ s, c.ι.app (.op s) ≫ base = (E s).hom ≫
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (N.obj s))))
    {Y : Scheme.{u}} (baseT : Y ⟶ Spec (.of T)) (q : Y ⟶ c.pt)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T)))) :
    scalarProjectiveNodeData N D E c baseT q := by
  let M := fixedFibreDiagram (R := T) (M := T) N
  let μ := fixedScalarMap S T N
  let old : ∀ s, line (N.obj s) ⟶ c.pt := fun s => (E s).inv ≫ c.ι.app (.op s)
  have holdOpen (s : J) : IsOpenImmersion (old s) := by
    let : IsOpenImmersion (c.ι.app (.op s)) := hopen s
    exact inferInstance
  have holdBase (s : J) : old s ≫ base = projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (N.obj s))) := by
    dsimp only [old]
    rw [Category.assoc, hbase s, Iso.inv_hom_id_assoc]
  choose K hOld hBase hCart hOpen using fun s =>
    @scalar_node S T (N.obj s) _ _ _ _ _ c.pt Y base baseT q hq (old s)
      (holdOpen s) (holdBase s)
  let : ∀ s, IsOpenImmersion (K s) := hOpen
  have htop : (⨆ s, (K s).opensRange) = ⊤ := by
    apply top_unique
    intro y _hy
    obtain ⟨s, z, hz⟩ := hcover c.pt (𝟙 c.pt) (q y)
    let x := pullback.snd (𝟙 c.pt) (c.ι.app (.op s)) z
    have hx : (c.ι.app (.op s)) x = q y := by
      have h := congrArg (fun f : pullback (𝟙 c.pt) (c.ι.app (.op s)) ⟶ c.pt => f z)
        (pullback.condition (f := 𝟙 c.pt) (g := c.ι.app (.op s)))
      exact h.symm.trans hz
    have he : (E s).inv ((E s).hom x) = x :=
      congrArg (fun f : D.obj (.op s) ⟶ D.obj (.op s) => f x) (E s).hom_inv_id
    have ho : old s ((E s).hom x) = q y :=
      (congrArg (fun x => (c.ι.app (.op s)) x) he).trans hx
    obtain ⟨w, _hw, hw⟩ := Scheme.exists_preimage_of_isPullback
      (hCart s) ((E s).hom x) y ho
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, ⟨w, hw⟩⟩
  refine ⟨K, hOld, hBase, hCart, hOpen, htop, ?_⟩
  intro s t f a b hd
  exact scalarAppend_projective_transition N M μ D E c f a b hd base baseT q hq
    (K s) (K t) (hOld s) (hOld t) (hBase s) (hBase t)

end SchubertGeometry.RetainedCharacter
