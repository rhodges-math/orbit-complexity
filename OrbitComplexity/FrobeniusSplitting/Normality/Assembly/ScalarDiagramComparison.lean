import OrbitComplexity.FrobeniusSplitting.Normality.Models.FixedDiagramIsos
import Batteries.Tactic.Lint

/-! # Scalar comparison families through an intermediate coefficient ring

The canonical cancellation isomorphism of fixed coefficient diagrams composes
with a prescribed field comparison at each object.
-/

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
universe u v w
open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

/-- Compose the canonical scalar-diagram cancellation with the given field
comparison family, retaining the original fixed-diagram object as source. -/
def scalarDiagramComparison {K : Type u} [kField : Field K]
    (S₀ S : Subalgebra ℤ K) (h : S₀ ≤ S)
    {J : Type v} [jCat : Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S₀) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ j, K ⊗[S₀] N.obj j ≃ₐ[K] F.obj j) :
    let kComm : CommRing K := @Field.toCommRing K kField
    let kRing : Ring K := @DivisionRing.toRing K (@Field.toDivisionRing K kField)
    let kSemi : CommSemiring K := @Semifield.toCommSemiring K (@Field.toSemifield K kField)
    let kSemiring : Semiring K := @CommSemiring.toSemiring K kSemi
    let zComm : CommRing ℤ := Int.instCommRing
    let zSemi : CommSemiring ℤ := Int.instCommSemiring
    let zAlg : Algebra ℤ K := @Ring.toIntAlgebra K kRing
    let s₀Comm : CommRing S₀ := @Subalgebra.toCommRing ℤ K zComm kComm zAlg S₀
    let sComm : CommRing S := @Subalgebra.toCommRing ℤ K zComm kComm zAlg S
    let s₀Semi : CommSemiring S₀ := @Subalgebra.toCommSemiring ℤ K zSemi kSemi zAlg S₀
    let sSemi : CommSemiring S := @Subalgebra.toCommSemiring ℤ K zSemi kSemi zAlg S
    let sSemiring : Semiring S := @CommSemiring.toSemiring S sSemi
    let inclusionMap := @Subalgebra.inclusion ℤ K zSemi kSemiring zAlg S₀ S h
    let inclusionRingMap := inclusionMap.toRingHom
    let inclusionAlg := @RingHom.toAlgebra S₀ S s₀Semi sSemi inclusionRingMap
    let sSelf : Algebra S S := @Algebra.id S sSemi
    let s₀SS := @IsScalarTower.right S₀ S s₀Semi sSemiring inclusionAlg
    ∀ j, K ⊗[S] (@fixedFibreDiagram.{u,v,w} J jCat S₀ S S
      s₀Comm sComm sComm inclusionAlg sSelf inclusionAlg s₀SS N).obj j ≃ₐ[K] F.obj j := by
  intro kComm kRing kSemi kSemiring zComm zSemi zAlg s₀Comm sComm s₀Semi sSemi
    sSemiring inclusionMap inclusionRingMap inclusionAlg sSelf s₀SS j
  let kSelf : Algebra K K := @Algebra.id K kSemi
  let s₀KAlg : Algebra S₀ K :=
    @Subalgebra.toAlgebra K ℤ K zSemi kSemi kSemiring zAlg kSelf S₀
  let sKAlg : Algebra S K :=
    @Subalgebra.toAlgebra K ℤ K zSemi kSemi kSemiring zAlg kSelf S
  let s₀KK := @IsScalarTower.right S₀ K s₀Semi kSemiring s₀KAlg
  let sKK := @IsScalarTower.right S K sSemi kSemiring sKAlg
  let kMonoid : Monoid K := @Semiring.toMonoid K kSemiring
  let kAction : MulAction K K := @Monoid.toMulAction K kMonoid
  let s₀SK := @Subalgebra.inclusion.isScalarTower_right
    ℤ K zSemi kSemiring zAlg S₀ S h K kAction
  let scalarN := @fixedFibreDiagram.{u,v,w} J jCat S₀ S S
    s₀Comm sComm sComm inclusionAlg sSelf inclusionAlg s₀SS N
  let fieldN := @fixedFibreDiagram.{u,v,w} J jCat S₀ K K
    s₀Comm kComm kComm s₀KAlg kSelf s₀KAlg s₀KK N
  let fieldScalarN := @fixedFibreDiagram.{u,v,w} J jCat S K K
    sComm kComm kComm sKAlg kSelf sKAlg sKK scalarN
  let cancellationIso := @fixedFibreCancelIso.{u,v,w} J jCat S₀ S K
    s₀Comm sComm kComm inclusionAlg sKAlg s₀KAlg s₀SK N
  let source : CommAlgCat.{u} K := fieldScalarN.obj j
  let middle : CommAlgCat.{u} K := fieldN.obj j
  let target : CommAlgCat.{u} K := F.obj j
  let component : source ≅ middle := cancellationIso.app j
  let cancellation := @CommAlgCat.algEquivOfIso.{u,u} K kComm source middle component
  let native := e j
  let sourceComm : CommRing source := @CommAlgCat.instCommRingObjForgetAlgHomCarrier K kComm source
  let middleComm : CommRing middle := @CommAlgCat.instCommRingObjForgetAlgHomCarrier K kComm middle
  let targetComm : CommRing target := @CommAlgCat.instCommRingObjForgetAlgHomCarrier K kComm target
  let sourceSemi : Semiring source :=
    @CommSemiring.toSemiring source (@CommRing.toCommSemiring source sourceComm)
  let middleSemi : Semiring middle :=
    @CommSemiring.toSemiring middle (@CommRing.toCommSemiring middle middleComm)
  let targetSemi : Semiring target :=
    @CommSemiring.toSemiring target (@CommRing.toCommSemiring target targetComm)
  let sourceAlg := @CommAlgCat.instAlgebraObjForgetAlgHomCarrier K kComm source
  let middleAlg := @CommAlgCat.instAlgebraObjForgetAlgHomCarrier K kComm middle
  let targetAlg := @CommAlgCat.instAlgebraObjForgetAlgHomCarrier K kComm target
  let combined := @AlgEquiv.trans.{u,u,u,u} K source middle target kSemi
    sourceSemi middleSemi targetSemi sourceAlg middleAlg targetAlg cancellation native
  exact combined

/-- The scalar comparison evaluates a pure tensor by multiplying its two
coefficient factors before applying the prescribed field comparison. -/
theorem scalarDiagramComparison_tmul {K : Type u} [kField : Field K]
    (S₀ S : Subalgebra ℤ K) (h : S₀ ≤ S)
    {J : Type v} [jCat : Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S₀) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ j, K ⊗[S₀] N.obj j ≃ₐ[K] F.obj j) :
    letI : Algebra S₀ S := (Subalgebra.inclusion h).toAlgebra
    ∀ (j : J) (k : K) (t : S) (x : N.obj j),
      (@scalarDiagramComparison.{u,v,w} K kField S₀ S h J jCat N F e j)
        (k ⊗ₜ[S] (t ⊗ₜ[S₀] x)) =
      e j ((algebraMap S K t * k) ⊗ₜ[S₀] x) := by
  let : Algebra S₀ S := (Subalgebra.inclusion h).toAlgebra
  intro j k t x
  let : IsScalarTower S₀ S K := Subalgebra.inclusion.isScalarTower_right h K
  change e j ((Algebra.TensorProduct.cancelBaseChange S₀ S K K (N.obj j))
    (k ⊗ₜ[S] (t ⊗ₜ[S₀] x))) = _
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]

/-- A natural prescribed field comparison remains natural after the
coefficient diagram is extended through an intermediate subalgebra. -/
theorem scalarDiagramComparison_natural {K : Type u} [kField : Field K]
    (S₀ S : Subalgebra ℤ K) (h : S₀ ≤ S)
    {J : Type v} [jCat : Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S₀) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ j, K ⊗[S₀] N.obj j ≃ₐ[K] F.obj j)
    (he : ∀ j j' (f : j ⟶ j'), (e j').toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e j).toAlgHom) :
    letI : Algebra S₀ S := (Subalgebra.inclusion h).toAlgebra
    let scalarN := fixedFibreDiagram (R := S) (M := S) N
    ∀ j j' (f : j ⟶ j'),
      (@scalarDiagramComparison.{u,v,w} K kField S₀ S h J jCat N F e j').toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (scalarN.map f).hom) =
      (F.map f).hom.comp
        (@scalarDiagramComparison.{u,v,w} K kField S₀ S h J jCat N F e j).toAlgHom := by
  let : Algebra S₀ S := (Subalgebra.inclusion h).toAlgebra
  intro scalarN j j' f
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k y =>
    induction y using TensorProduct.inductionOn with
    | tmul t x =>
      change (@scalarDiagramComparison.{u,v,w} K kField S₀ S h J jCat N F e j')
          (k ⊗ₜ[S] (t ⊗ₜ[S₀] (N.map f).hom x)) =
        (F.map f).hom
          ((@scalarDiagramComparison.{u,v,w} K kField S₀ S h J jCat N F e j)
            (k ⊗ₜ[S] (t ⊗ₜ[S₀] x)))
      rw [@scalarDiagramComparison_tmul.{u,v,w} K kField S₀ S h J jCat N F e j' k t,
        @scalarDiagramComparison_tmul.{u,v,w} K kField S₀ S h J jCat N F e j k t]
      exact congrArg (fun g => g ((algebraMap S K t * k) ⊗ₜ[S₀] x)) (he j j' f)
    | add y y' hy hy' =>
      simpa only [TensorProduct.tmul_add, AlgHom.comp_apply, map_add] using
        congrArg₂ (· + ·) hy hy'
  | add z z' hz hz' =>
    simpa only [AlgHom.comp_apply, map_add] using congrArg₂ (· + ·) hz hz'


end FrobeniusSplitting
