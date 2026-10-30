import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Borel.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-! # Hopf ideals over algebraically closed fields

Base change along a field isomorphism is surjective on Hopf ideals. In particular, over an
algebraically closed field, Borel minimality and the normal-unipotent criterion for reductivity
can be checked before passage to its algebraic closure.
-/

open CategoryTheory TauCeti
open scoped TensorProduct

noncomputable section
universe u
namespace ReductiveGroups.HopfIdeals
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable [Algebra L k] [IsScalarTower k L k]

private def backChangeIso (H : CommHopfAlgCat.{u} k) :
    CommHopfAlgCat.baseChange (K := k) (CommHopfAlgCat.baseChange (K := L) H) ≅ H :=
  CommHopfAlgCat.baseChangeTowerIso k k H ≪≫
    CommHopfAlgCat.isoMk (_root_.Bialgebra.TensorProduct.lid k H)

private def descendIdeal (H : CommHopfAlgCat.{u} k)
    (J : HopfIdeal L (CommHopfAlgCat.baseChange (K := L) H)) : HopfIdeal k H :=
  (CommHopfAlgCat.baseChangeHopfIdeal (K := k) J).map (backChangeIso (L := L) H).hom.hom

private theorem backChangeIso_unit (H : CommHopfAlgCat.{u} k) (h : H) :
    (backChangeIso (L := L) H).hom.hom ((1 : k) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] h)) = h := by
  change _root_.Bialgebra.TensorProduct.lid k H
    (TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k L H k
      ((1 : k) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] h))) = h
  rw [TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul]
  simp only [one_smul, _root_.Bialgebra.TensorProduct.lid_tmul]

private theorem descendIdeal_spec (H : CommHopfAlgCat.{u} k)
    (hb : Function.Bijective (algebraMap k L))
    (J : HopfIdeal L (CommHopfAlgCat.baseChange (K := L) H)) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := L) (descendIdeal H J) = J := by
  let a : H →+* L ⊗[k] H := Algebra.TensorProduct.includeRight.toRingHom
  let b : L ⊗[k] H →+* H :=
    (backChangeIso (L := L) H).hom.hom.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        CommHopfAlgCat.baseChange (K := L) H →ₐ[L]
          k ⊗[L] CommHopfAlgCat.baseChange (K := L) H).toRingHom
  have hab : a.comp b = RingHom.id _ := by
    apply RingHom.ext
    intro x
    obtain ⟨h, rfl⟩ := (Algebra.TensorProduct.includeRight_bijective hb).2 x
    change a ((backChangeIso (L := L) H).hom.hom
      ((1 : k) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] h))) = a h
    rw [backChangeIso_unit]
  have hi : (CommHopfAlgCat.baseChangeHopfIdeal (K := L) (descendIdeal H J)).toIdeal =
      J.toIdeal := by
    rw [CommHopfAlgCat.baseChangeHopfIdeal_toIdeal, descendIdeal, HopfIdeal.map_toIdeal,
      CommHopfAlgCat.baseChangeHopfIdeal_toIdeal]
    change Ideal.map a
      (Ideal.map (backChangeIso (L := L) H).hom.hom.toAlgHom.toRingHom
        (Ideal.map (Algebra.TensorProduct.includeRight :
          CommHopfAlgCat.baseChange (K := L) H →ₐ[L]
            k ⊗[L] CommHopfAlgCat.baseChange (K := L) H).toRingHom J.toIdeal)) = J.toIdeal
    rw [Ideal.map_map, Ideal.map_map]
    change Ideal.map (a.comp b) J.toIdeal = J.toIdeal
    rw [hab, Ideal.map_id]
  apply HopfIdeal.ext
  intro x
  change x ∈ (CommHopfAlgCat.baseChangeHopfIdeal (K := L) (descendIdeal H J)).toIdeal ↔
    x ∈ J.toIdeal
  rw [hi]

omit [Algebra L k] [IsScalarTower k L k] in
/-- Base change along an isomorphism of fields is surjective on Hopf ideals. -/
theorem baseChange_surjective (H : CommHopfAlgCat.{u} k)
    (hb : Function.Bijective (algebraMap k L)) :
    Function.Surjective (CommHopfAlgCat.baseChangeHopfIdeal (K := L) (H := H)) := by
  let e : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L) hb
  let : Algebra L k := e.symm.toRingHom.toAlgebra
  let : IsScalarTower k L k :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.symm.commutes x).symm
  intro J
  exact ⟨descendIdeal H J, descendIdeal_spec H hb J⟩


omit [Algebra L k] [IsScalarTower k L k] in
private theorem candidate_baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) (hI : HopfIdeal.IsBorelCandidate k H I) :
    HopfIdeal.IsBorelCandidate L (FiniteTypeCommHopfAlgCat.baseChange (K := L) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := L) I) := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := L) I
  let : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I) :=
    (smoothCommHopfAlgProperty_iff _).mp hI.smooth
  refine HopfIdeal.IsBorelCandidate.mk ?_ ?_ ?_
  · apply (smoothCommHopfAlgProperty L).prop_of_iso qIso.symm
    exact (smoothCommHopfAlgProperty_iff _).mpr inferInstance
  · exact (geometricallyConnectedCommHopfAlgProperty L).prop_of_iso qIso.symm
      (geometricallyConnectedCommHopfAlgProperty.baseChange k L
        (FiniteTypeCommHopfAlgCat.quotient H I).obj hI.geometricallyConnected)
  · exact (geometricallySolvablePointsCommHopfAlgProperty L).prop_of_iso qIso.symm
      (geometricallySolvablePointsCommHopfAlgProperty.baseChange (K := L)
        (FiniteTypeCommHopfAlgCat.quotient H I).obj hI.geometricallySolvable)

omit [Algebra k L] [Algebra L k] [IsScalarTower k L k] in
/-- Over an algebraically closed field, ground-field Borel minimality is geometric. -/
theorem isBorel_of_algClosed [IsAlgClosed k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) (hI : HopfIdeal.IsBorelOverAlgClosed k H I) :
    HopfIdeal.IsBorel k H.obj I := by
  change HopfIdeal.IsBorelOverAlgClosed (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
    (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I)
  refine ⟨inferInstance, candidate_baseChange H I hI.2.1, ?_⟩
  intro J hJ hJI
  obtain ⟨J0, hJ0⟩ := baseChange_surjective H.obj
    (L := AlgebraicClosure k) IsAlgClosed.algebraMap_bijective_of_isIntegral J
  have hCand : HopfIdeal.IsBorelCandidate k H J0 := by
    apply HopfIdeal.IsBorelCandidate.of_baseChange (K := AlgebraicClosure k)
    simpa only [hJ0] using hJ
  have hle : J0 ≤ I :=
    (CommHopfAlgCat.baseChangeHopfIdeal_le_iff
      (J := J0) (J' := I)
      (RingHom.injective (algebraMap k (AlgebraicClosure k)))).mp (by
        rw [hJ0]
        exact hJI)
  have hIJ : I ≤ J0 := hI.2.2 hCand hle
  rw [← hJ0]
  exact CommHopfAlgCat.baseChangeHopfIdeal_mono hIJ


private def descendQuotientIso (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (J : HopfIdeal L (FiniteTypeCommHopfAlgCat.baseChange (K := L) H)) :
    FiniteTypeCommHopfAlgCat.quotient H (descendIdeal H.obj J) ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := k)
        (FiniteTypeCommHopfAlgCat.quotient
          (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) J) := by
  let D := FiniteTypeCommHopfAlgCat.baseChange (K := k)
    (FiniteTypeCommHopfAlgCat.baseChange (K := L) H)
  let e : D ≅ H := ObjectProperty.isoMk _ (backChangeIso (L := L) H.obj)
  let J0 := CommHopfAlgCat.baseChangeHopfIdeal (K := k) J
  let I := descendIdeal H.obj J
  have hcomap : I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom).2 = J0 := by
    exact HopfIdeal.comapOfSurjective_map_of_bijective J0
      (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom)
  exact (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I).symm ≪≫
    eqToIso (congrArg (FiniteTypeCommHopfAlgCat.quotient D) hcomap) ≪≫
      ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBaseChangeIso (K := k) J)

private theorem descend_connected (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (J : HopfIdeal L (FiniteTypeCommHopfAlgCat.baseChange (K := L) H))
    (hJ : geometricallyConnectedCommHopfAlgProperty L
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) J).obj) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H (descendIdeal H.obj J)).obj := by
  let e := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k) (CommHopfAlgCat.{u} k)).mapIso
    (descendQuotientIso H J)
  exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
    (geometricallyConnectedCommHopfAlgProperty.baseChange L k
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) J).obj hJ)

private theorem descend_unipotent (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (J : HopfIdeal L (FiniteTypeCommHopfAlgCat.baseChange (K := L) H))
    (hJ : smoothUnipotentCommHopfAlgProperty L
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) J)) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H (descendIdeal H.obj J)) := by
  exact (smoothUnipotentCommHopfAlgProperty k).prop_of_iso (descendQuotientIso H J).symm
    (smoothUnipotentCommHopfAlgProperty.baseChange
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) J) hJ)


private theorem descend_normal (H : CommHopfAlgCat.{u} k)
    (J : HopfIdeal L (CommHopfAlgCat.baseChange (K := L) H)) (hJ : J.IsNormal) :
    (descendIdeal H J).IsNormal :=
  (CommHopfAlgCat.isNormal_baseChangeHopfIdeal (K := k) hJ).map
    (backChangeIso (L := L) H).hom.hom

omit [Algebra k L] [Algebra L k] [IsScalarTower k L k] in
/-- Over an algebraically closed field, ground normal-unipotent triviality implies reductivity. -/
theorem reductive_of_ground [IsAlgClosed k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hsmooth : Algebra.Smooth k H)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj)
    (hfree : ∀ J : HopfIdeal k H, J.IsNormal →
      geometricallyConnectedCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient H J).obj →
      smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H J) →
      J = HopfIdeal.augmentation k H) :
    reductiveCommHopfAlgProperty k H := by
  rw [reductiveCommHopfAlgProperty_iff]
  refine ⟨hsmooth, hconnected, ?_⟩
  intro J hnormal hconn hunip
  let e : k ≃ₐ[k] AlgebraicClosure k := AlgEquiv.ofBijective
    (Algebra.ofId k (AlgebraicClosure k)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let : Algebra (AlgebraicClosure k) k := e.symm.toRingHom.toAlgebra
  let : IsScalarTower k (AlgebraicClosure k) k :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.symm.commutes x).symm
  have hground := hfree (descendIdeal H.obj J) (descend_normal H.obj J hnormal)
    (descend_connected H J hconn) (descend_unipotent H J hunip)
  calc
    J = CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
        (descendIdeal H.obj J) :=
      (descendIdeal_spec H.obj IsAlgClosed.algebraMap_bijective_of_isIntegral J).symm
    _ = CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
        (HopfIdeal.augmentation k H) :=
      congrArg (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)) hground
    _ = HopfIdeal.augmentation (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
      CommHopfAlgCat.baseChangeHopfIdeal_augmentation

end ReductiveGroups.HopfIdeals
