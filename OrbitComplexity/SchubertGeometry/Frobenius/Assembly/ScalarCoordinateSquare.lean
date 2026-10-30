import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.FixedPriorProjection
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateSquare
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The retained coordinate projection on the same proper model

The two coefficient extensions are compared with the single extension by tensor
cancellation. The geometric projection of that single extension determines the
projection of the retained diagram through its affine coordinate equations.
Both the scalar square and the original model projection are retained.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

noncomputable section

universe u v w

namespace SchubertGeometry.RetainedCharacter

open private cartesian_transport
  from OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateSquare
open private inverseOpenDiagram fieldSchemeDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison

private theorem tower_evaluation {S T R K A B : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    [Algebra R K] [Algebra T K] [Algebra S K]
    [IsScalarTower T R K]
    [Algebra S A] [Algebra K B]
    (e : K ⊗[S] A ≃ₐ[K] B)
    (eT : K ⊗[T] (T ⊗[S] A) ≃ₐ[K] B)
    (eR : K ⊗[R] (R ⊗[S] A) ≃ₐ[K] B)
    (hT : ∀ k t x, eT (k ⊗ₜ[T] (t ⊗ₜ[S] x)) = e ((algebraMap T K t * k) ⊗ₜ[S] x))
    (hR : ∀ k r x, eR (k ⊗ₜ[R] (r ⊗ₜ[S] x)) = e ((algebraMap R K r * k) ⊗ₜ[S] x))
    (x : R ⊗[T] (T ⊗[S] A)) :
    eT (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
      (AlgHom.id T (T ⊗[S] A)) x) =
      eR ((1 : K) ⊗ₜ[R] Algebra.TensorProduct.cancelBaseChange S T R R A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r y =>
    induction y using TensorProduct.inductionOn with
    | tmul t z =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hT,
        Algebra.TensorProduct.cancelBaseChange_tmul, hR]
      apply congrArg e
      apply congrArg (fun k : K => k ⊗ₜ[S] z)
      simp only [IsScalarTower.toAlgHom_apply, Algebra.smul_def, map_mul,
        mul_one, IsScalarTower.algebraMap_apply T R K]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

private theorem retained_evaluation_factor {S T R K A B : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    [Algebra R K] [Algebra T K] [Algebra S K]
    [IsScalarTower T R K]
    [Algebra S A] [Algebra K B]
    (e : K ⊗[S] A ≃ₐ[K] B)
    (eT : K ⊗[T] (T ⊗[S] A) ≃ₐ[K] B)
    (eR : K ⊗[R] (R ⊗[S] A) ≃ₐ[K] B)
    (hT : ∀ k t x, eT (k ⊗ₜ[T] (t ⊗ₜ[S] x)) = e ((algebraMap T K t * k) ⊗ₜ[S] x))
    (hR : ∀ k r x, eR (k ⊗ₜ[R] (r ⊗ₜ[S] x)) = e ((algebraMap R K r * k) ⊗ₜ[S] x))
    (v : R ⊗[T] (T ⊗[S] A) →+* B)
    (hv : ∀ x, v x = eT (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
      (AlgHom.id T (T ⊗[S] A)) x)) :
    v = (eR.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).comp
      (Algebra.TensorProduct.cancelBaseChange S T R R A).toRingHom := by
  apply RingHom.ext
  intro x
  exact (hv x).trans (@tower_evaluation S T R K A B
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance e eT eR hT hR x)

/-- The retained nested coefficient diagram has a cocone on the same point
as the single coefficient extension of the original proper model. -/
def retainedCoordinateCocone {I : Type v} [Category.{w} I]
    {S T R : Type u} [CommRing S] [CommRing T] [CommRing R]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    (M : I ⥤ CommAlgCat.{u} S)
    (c : Cocone ((fixedFibreDiagram (R := R) (M := R) M).op ⋙ algSpec (.of R))) :
    Cocone ((fixedFibreDiagram (R := R) (M := R)
      (fixedFibreDiagram (R := T) (M := T) M)).op ⋙ algSpec (.of R)) where
  pt := c.pt
  ι := (Functor.isoWhiskerRight
    (NatIso.op (fixedFibreCancelIso (T := T) (R := R) M)).symm (algSpec (.of R))).hom ≫ c.ι

private theorem spec_factor {A B D : CommRingCat.{u}}
    (a : A ≅ B) (i : Spec A ≅ Spec B) (hi : i.inv = Spec.map a.hom)
    (v : A ⟶ D) (w : B ⟶ D) (hv : v.hom = w.hom.comp a.hom.hom) :
    Spec.map v = Spec.map w ≫ i.inv := by
  have hv' : v = a.hom ≫ w := CommRingCat.hom_ext hv
  calc
    Spec.map v = Spec.map (a.hom ≫ w) := congrArg Spec.map hv'
    _ = Spec.map w ≫ Spec.map a.hom := Spec.map_comp _ _
    _ = Spec.map w ≫ i.inv := congrArg (fun f => Spec.map w ≫ f) hi.symm

private theorem mapped_extended_leg {I C D : Type*}
    [Category I] [Category C] [Category D] {E : I ⥤ C}
    (F : C ⥤ D) (c : Cocone E) {X : C} (e : c.pt ≅ X) (j : I) :
    (F.mapCocone (c.extend e.hom)).ι.app j =
      F.map (c.ι.app j) ≫ (F.mapIso e).hom := by
  change F.map (c.ι.app j ≫ e.hom) = F.map (c.ι.app j) ≫ F.map e.hom
  exact F.map_comp _ _

private theorem reindexed_node {C : Type*} [Category C]
    {A B D P Q X : C} (i : B ≅ D) (v : A ⟶ B) (w : A ⟶ D)
    (lN : B ⟶ P) (l₀ : D ⟶ P) (lF : A ⟶ Q) (e : Q ⟶ X) (m : X ⟶ P)
    (b : A ⟶ X) (hN : lN = i.hom ≫ l₀) (hv : v = w ≫ i.inv)
    (hm : b ≫ m = w ≫ l₀) (hb : b = lF ≫ e) :
    v ≫ lN = lF ≫ (e ≫ m) := by
  rw [hN, hv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact hm.symm.trans ((congrArg (fun f ↦ f ≫ m) hb).trans (Category.assoc _ _ _))

private theorem reindexed_projection
    {R K : Type u} [CommRing R] [CommRing K]
    {J : Type v} [Category.{w} J]
    (N N₀ : J ⥤ CommAlgCat.{u} R) (F : J ⥤ CommAlgCat.{u} K)
    (α : N ≅ N₀) (c₀ : Cocone (N₀.op ⋙ algSpec (.of R)))
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (w : ∀ s, (forget₂ (CommAlgCat R) CommRingCat).obj (N₀.obj s) ⟶
      (forget₂ (CommAlgCat K) CommRingCat).obj (F.obj s))
    {X : Scheme.{u}} (eF : cF.pt.left ≅ X)
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj X)
    (hb : ∀ s, b.app s = (cF.ι.app s).left ≫ eF.hom)
    (m : X ⟶ c₀.pt.left)
    (hm : ∀ s, b.app (op s) ≫ m = Spec.map (w s) ≫ (c₀.ι.app (op s)).left)
    (hfactor : ∀ s, (v.app s).hom = (w s).hom.comp
      ((forget₂ (CommAlgCat R) CommRingCat).map (α.hom.app s)).hom) :
    let θ := Functor.isoWhiskerRight (NatIso.op α).symm (algSpec (.of R))
    let cN : Cocone (N.op ⋙ algSpec (.of R)) :=
      { pt := c₀.pt, ι := θ.hom ≫ c₀.ι }
    scalarModelProjection N F v cN cF hcF = eF.hom ≫ m := by
  intro θ cN
  apply scalarModelProjection_unique
  intro s
  let a := (forget₂ (CommAlgCat R) CommRingCat).mapIso (α.app s)
  let i := (Over.forget (Spec (.of R))).mapIso (θ.app (op s))
  have hSpec := spec_factor a i rfl (v.app s) (w s) (hfactor s)
  exact @reindexed_node Scheme.{u} Scheme.instCategory
    ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))).obj (op s))
    ((N.op ⋙ algSpec (.of R)).obj (op s)).left
    ((N₀.op ⋙ algSpec (.of R)).obj (op s)).left
    c₀.pt.left cF.pt.left X i (Spec.map (v.app s)) (Spec.map (w s))
    (cN.ι.app (op s)).left (c₀.ι.app (op s)).left (cF.ι.app (op s)).left
    eF.hom m (b.app (op s)) rfl hSpec (hm s) (hb (op s))

private theorem close_projection {C : Type*} [Category C]
    {A B X Y S T : C} (q : A ⟶ B) (e : A ≅ X)
    (baseX : X ⟶ T) (baseA : A ⟶ T) (baseB : B ⟶ S) (k : T ⟶ S)
    (pB : B ⟶ Y) (pX : X ⟶ Y) (P : (X ⟶ B) → Prop)
    (h : ∃ m : X ⟶ B, IsPullback m baseX baseB k ∧ m ≫ pB = pX ∧ P m)
    (identify : ∀ m, P m → q = e.hom ≫ m)
    (he : e.hom ≫ baseX = baseA) :
    IsPullback q baseA baseB k ∧ q ≫ pB = e.hom ≫ pX := by
  obtain ⟨m, hcart, hp, hP⟩ := h
  have hq := identify m hP
  refine ⟨cartesian_transport m baseX baseB k hcart (Iso.refl B) e q baseA baseB
    (by simpa only [Iso.refl_inv, Category.comp_id] using hq) he (Category.id_comp _), ?_⟩
  exact (congrArg (fun f => f ≫ pB) hq).trans
    ((Category.assoc _ _ _).trans (congrArg (fun f => e.hom ≫ f) hp))

set_option cleanup.letToHave false in
/-- The prescribed retained projection has the geometric scalar square and
preserves the projection to the original proper model. -/
theorem retainedCoordinateProjection {K : Type u} [kField : Field K]
    (S T R : Subalgebra ℤ K) (hST : S ≤ T) (hTR : T ≤ R) :
    letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    letI : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
    letI : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
    letI : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
    letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
    ∀ {Y X : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (_hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {I : Type u} (U : I → Y.Opens) (_hU : ∀ j, IsAffineOpen (U j)),
    let B := intersectionOpens U
    let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} S
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
      Y base {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let N₀ := fixedFibreDiagram (R := R) (M := R) M
    let N := fixedFibreDiagram (R := R) (M := R)
      (fixedFibreDiagram (R := T) (M := T) M)
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    let VR := @inverseOpenDiagram.{u,u,u} Y YR qR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let VK := @inverseOpenDiagram.{u,u,u} Y X qK
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let ER := @fieldSchemeDiagram.{u,u,u} R
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
      YR baseR {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VR
    let EK := @fieldSchemeDiagram.{u,u,u} K
      (@Field.toCommRing K kField) X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VK
    let CR := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} R
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
      YR baseR {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VR
    let F := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VK
    let vR : ∀ s, M.obj s →+* CR.obj s :=
      fun s => (qR ∣_ B.obj (op s)).appTop.hom
    let vK : ∀ s, M.obj s →+* F.obj s :=
      fun s => (qK ∣_ B.obj (op s)).appTop.hom
    ∀ (hER : ∀ s, IsAffine (ER.obj s).left) (hEK : ∀ s, IsAffine (EK.obj s).left),
    letI := hER
    letI := hEK
    ∀ (d : N₀ ≅ CR) (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
      (c₀ : Cocone (N₀.op ⋙ algSpec (.of R))) (_hc₀ : IsColimit c₀)
      (hpt₀ : c₀.pt = Over.mk baseR)
      (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
      (hptF : cF.pt = Over.mk baseK)
      (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat),
      (∀ s r x, (d.hom.app s).hom (r ⊗ₜ[S] x) =
        algebraMap R (CR.obj s) r * vR s x) →
      (∀ s k x, e s (k ⊗ₜ[S] x) =
        algebraMap K (F.obj s) k * vK s x) →
      (∀ s, (c₀.ι.app s ≫ eqToHom hpt₀).left =
        Spec.map (CommRingCat.ofHom (d.inv.app s.unop).hom.toRingHom) ≫
          ((coordinateDiagramIso (.of R) ER).inv.app s).left ≫ (VR.obj s).ι) →
      (∀ s, (cF.ι.app s ≫ eqToHom hptF).left =
        ((coordinateDiagramIso (.of K) EK).inv.app s).left ≫ (VK.obj s).ι) →
      (∀ s x, (v.app s).hom x =
        (@scalarDiagramComparison.{u,u,u} K kField S T hST {s : Finset I // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e s)
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
            (AlgHom.id T (T ⊗[S] M.obj s)) x)) →
      let cN := retainedCoordinateCocone (T := T) M c₀
      Nonempty (IsColimit cN) ∧
      IsPullback (scalarModelProjection N F v cN cF hcF) cF.pt.hom cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      scalarModelProjection N F v cN cF hcF ≫ (eqToHom hpt₀).left ≫ qR =
        (eqToHom hptF).left ≫ qK := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  intro Y X base baseProper baseK qK hK I U hU B M N₀ N sr YR qR baseR VR VK ER EK CR F vR vK hER
      hEK
  let : ∀ s, IsAffine (ER.obj s).left := hER
  let : ∀ s, IsAffine (EK.obj s).left := hEK
  dsimp only
  intro d e c₀ hc₀ hpt₀ cF hcF hptF v hd he hl₀ hlF hv
  let α := fixedFibreCancelIso (T := T) (R := R) M
  let θ := Functor.isoWhiskerRight (NatIso.op α).symm (algSpec (.of R))
  let cN := retainedCoordinateCocone (T := T) M c₀
  let b := ((Over.forget (Spec (.of K))).mapCocone
    (cF.extend (eqToHom hptF))).ι
  have hb : IsColimit (Cocone.mk X b) :=
    isColimitOfPreserves (Over.forget (Spec (.of K)))
      (IsColimit.extendIso (eqToHom hptF) hcF)
  let eF : cF.pt.left ≅ X := (Over.forget (Spec (.of K))).mapIso (eqToIso hptF)
  have hbaseF : eF.hom ≫ baseK = cF.pt.hom := (eqToHom hptF).w
  let eR := @scalarDiagramComparison.{u,u,u} K kField S R (hST.trans hTR)
    {s : Finset I // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
  have heR := @scalarDiagramComparison_tmul.{u,u,u} K kField S R (hST.trans hTR)
    {s : Finset I // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
  have H := @project_fixed_prior.{u} K kField S R (hST.trans hTR)
    Y X base baseProper baseK qK hK I U hU hER hEK d e eR c₀ hpt₀ b hb hd he heR hl₀ hlF
  refine ⟨⟨(IsColimit.precomposeHomEquiv θ c₀).symm hc₀⟩, ?_⟩
  exact @close_projection Scheme.{u} Scheme.instCategory cF.pt.left c₀.pt.left X Y
    (Spec (.of R)) (Spec (.of K)) (scalarModelProjection N F v cN cF hcF) eF
    baseK cF.pt.hom c₀.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    ((eqToHom hpt₀).left ≫ qR) qK _ H
    (fun m hm => by
      have hidentify := @reindexed_projection.{u,u,u} R K
        (inferInstanceAs (CommRing R)) (inferInstanceAs (CommRing K))
        {s : Finset I // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty}))
        N N₀ F α c₀ cF hcF v
        (fun s => CommRingCat.ofHom ((eR s).toRingHom.comp
          Algebra.TensorProduct.includeRight.toRingHom))
        X eF b
        (fun s => mapped_extended_leg (Over.forget (Spec (.of K))) cF
          (eqToIso hptF) s)
        m hm
        (fun s => by
          have hfactor := @retained_evaluation_factor.{u} S T R K (M.obj s) (F.obj s)
            inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
            inferInstance inferInstance inferInstance inferInstance
            inferInstance inferInstance inferInstance inferInstance
            inferInstance inferInstance (e s)
            (@scalarDiagramComparison.{u,u,u} K kField S T hST {s : Finset I // s.Nonempty}
              (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e s)
            (eR s)
            (fun k t x => @scalarDiagramComparison_tmul.{u,u,u} K kField S T hST {s : Finset I //
                s.Nonempty}
              (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e s k t x)
            (heR s)
            (v.app s).hom (hv s)
          exact hfactor)
      exact hidentify) hbaseF
end SchubertGeometry.RetainedCharacter
