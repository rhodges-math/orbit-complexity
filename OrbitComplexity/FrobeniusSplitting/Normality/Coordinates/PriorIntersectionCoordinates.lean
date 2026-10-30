import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorRefinedCover
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones

/-! # The chosen prior intersection diagram and its generic fibre -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
noncomputable section
universe u v w
namespace FrobeniusSplitting

private theorem diagram_coordinates {C : Type v} [Category.{w} C]
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (ER : Cᵒᵖ ⥤ Over (Spec (.of R))) (EK : Cᵒᵖ ⥤ Over (Spec (.of K)))
    (q : EK ⋙ Over.forget _ ⟶ ER ⋙ Over.forget _)
    (haff : ∀ s, IsAffine (ER.obj s).left)
    (hcart : ∀ s, IsPullback (q.app s) (EK.obj s).hom (ER.obj s).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    let N := (ER ⋙ algΓ (.of R)).unop
    let F := (EK ⋙ algΓ (.of K)).unop
    let v : ∀ s, N.obj s →+* F.obj s := fun s ↦ (q.app (.op s)).appTop.hom
    ∃ e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s,
      (∀ s k x, e s (k ⊗ₜ[R] x) =
        algebraMap K (F.obj s) k * v s x) ∧
      ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom := by
  let N := (ER ⋙ algΓ (.of R)).unop
  let F := (EK ⋙ algΓ (.of K)).unop
  let v : ∀ s, N.obj s →+* F.obj s := fun s ↦ (q.app (.op s)).appTop.hom
  have coords (s : C) : ∃ e : K ⊗[R] N.obj s ≃ₐ[K] F.obj s,
      (∀ k, e (k ⊗ₜ[R] (1 : N.obj s)) = algebraMap K (F.obj s) k) ∧
      (∀ x, e ((1 : K) ⊗ₜ[R] x) = v s x) ∧
      ∀ k x, e (k ⊗ₜ[R] x) =
        algebraMap K (F.obj s) k * v s x := by
    have : IsAffine (ER.obj (.op s)).left := haff (.op s)
    exact exists_affine_scalar_coordinates (ER.obj (.op s)).hom (EK.obj (.op s)).hom
      (q.app (.op s)) (hcart (.op s))
  choose e hleft hright he using coords
  refine ⟨e, he, fun s t f ↦ ?_⟩
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k x =>
      change e t (k ⊗ₜ[R] (N.map f).hom x) = (F.map f).hom (e s (k ⊗ₜ[R] x))
      rw [he, he, map_mul, (F.map f).hom.commutes]
      have H := congrArg
        (fun g : (EK.obj (.op t)).left ⟶ (ER.obj (.op s)).left ↦ g.appTop.hom x)
        (q.naturality f.op)
      exact congrArg (fun y : F.obj t ↦ algebraMap K (F.obj t) k * y) H.symm
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The intersection coordinate rings of the same proper prior model admit their
generic tensor comparisons, naturally for every restriction arrow. -/
theorem prior_intersection_coordinates {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {Y YK : Scheme.{u}} (base : Y ⟶ Spec (.of R)) [IsProper base]
    (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ Y)
    (h : IsPullback m baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {I : Type u} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    let J := {s : Finset I // s.Nonempty}
    let B := intersectionOpens U
    let V : Jᵒᵖ ⥤ YK.Opens :=
      { obj := fun s ↦ m ⁻¹ᵁ B.obj s
        map := fun f ↦ homOfLE (m.preimage_mono (leOfHom (B.map f))) }
    let ER := B ⋙ Y.restrictFunctor ⋙ Over.map base
    let EK := V ⋙ YK.restrictFunctor ⋙ Over.map baseK
    let N := (ER ⋙ algΓ (.of R)).unop
    let F := (EK ⋙ algΓ (.of K)).unop
    let v : ∀ s : J, N.obj s →+* F.obj s := fun s ↦ (m ∣_ B.obj (.op s)).appTop.hom
    ∃ e : ∀ s : J, K ⊗[R] N.obj s ≃ₐ[K] F.obj s,
      (∀ s k x, e s (k ⊗ₜ[R] x) = algebraMap K (F.obj s) k * v s x) ∧
      ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom := by
  let J := {s : Finset I // s.Nonempty}
  let B := intersectionOpens U
  let V : Jᵒᵖ ⥤ YK.Opens :=
    { obj := fun s ↦ m ⁻¹ᵁ B.obj s
      map := fun f ↦ homOfLE (m.preimage_mono (leOfHom (B.map f))) }
  let ER := B ⋙ Y.restrictFunctor ⋙ Over.map base
  let EK := V ⋙ YK.restrictFunctor ⋙ Over.map baseK
  have : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from base]
    infer_instance⟩
  have haff (s : Jᵒᵖ) : IsAffine (ER.obj s).left := intersectionOpens_affine U hU s
  let q : EK ⋙ Over.forget _ ⟶ ER ⋙ Over.forget _ :=
    { app := fun s ↦ m ∣_ B.obj s
      naturality := by
        intro s t f
        exact (morphismRestrict_homOfLE m (B.obj s) (B.obj t) (leOfHom (B.map f))).symm }
  have hcart (s : Jᵒᵖ) : IsPullback (q.app s) (EK.obj s).hom (ER.obj s).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (isPullback_morphismRestrict m (B.obj s)).paste_vert h
  exact diagram_coordinates ER EK q haff hcart

end FrobeniusSplitting
