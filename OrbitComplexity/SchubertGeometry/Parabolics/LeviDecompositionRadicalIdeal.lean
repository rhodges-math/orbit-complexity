import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionMaps
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootUnipotent
import OrbitComplexity.ReductiveGroups.Groups.Hopf.ReducedPointNormality
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-! # Root-factor ideals in parabolic coordinate algebras

The quotient map to the outside-subsystem positive-root group defines its closed
subgroup ideal in the parabolic coordinate algebra.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem normal_of_points {B : Type u} [CommRing B] [HopfAlgebra K B]
    [Algebra.FiniteType K B] [IsReduced B] (J : HopfIdeal K B)
    [IsReduced (B ⧸ J.toIdeal)]
    (hn : (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of K B) J
      (CommAlgCat.of K K)).Normal) : J.IsNormal := by
  apply isNormal_of_point_conjugation_stable (K := K) (B := B) J
  intro g b hb
  apply HopfIdeal.mem_toIdeal.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro x
  let n : WithConv (B →ₐ[K] K) :=
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of K B) J
      (CommAlgCat.of K K) (toConv x)
  have hnmem : n ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of K B) J
      (CommAlgCat.of K K) :=
    CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _
  have hc : g * n * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of K B) J (CommAlgCat.of K K) := hn.conj_mem n hnmem g
  have hz : (g * n * g⁻¹).ofConv b = 0 :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff (_root_.CommHopfAlgCat.of K B) J
      (CommAlgCat.of K K) (g * n * g⁻¹)).mp hc b hb
  have hp := affineGroupConjugationAlgHom_point g n
  have hs : (IsScalarTower.toAlgHom K K K).comp g.ofConv = g.ofConv := by
    ext a
    simp
  have he : toConv (n.ofConv.comp (affineGroupConjugationAlgHom g)) = g * n * g⁻¹ := by
    simpa only [hs, toConv_ofConv] using hp
  have hz' : n.ofConv (affineGroupConjugationAlgHom g b) = 0 :=
    (congrArg (fun p : WithConv (B →ₐ[K] K) => p.ofConv b) he).trans hz
  exact hz'.trans (map_zero x).symm


omit [IsAlgClosed K] [CharZero K] in
private theorem kernel_points_range {A B : _root_.CommHopfAlgCat.{u} K} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) (g : WithConv (A →ₐ[K] K)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup A
      (HopfIdeal.kerOfSurjective f.hom hf) (CommAlgCat.of K K) ↔
        ∃ x : WithConv (B →ₐ[K] K), AlgHom.mapDomain f.hom x = g := by
  constructor
  · rintro ⟨x, hx⟩
    let e := CommHopfAlgCat.quotientKerOfSurjectiveIso f hf
    refine ⟨AlgHom.mapDomain e.inv.hom x, ?_⟩
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    have he := congrArg (fun z : A ⟶ B => z.hom a)
      (CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom f hf)
    have hi := congrArg (fun z : (CommHopfAlgCat.quotient A
        (HopfIdeal.kerOfSurjective f.hom hf)) ⟶
        CommHopfAlgCat.quotient A (HopfIdeal.kerOfSurjective f.hom hf) =>
          z.hom ((CommHopfAlgCat.mkQuotient A (HopfIdeal.kerOfSurjective f.hom hf)).hom a))
      e.hom_inv_id
    have he' : e.inv.hom (f.hom a) =
        (CommHopfAlgCat.mkQuotient A (HopfIdeal.kerOfSurjective f.hom hf)).hom a :=
      (congrArg e.inv.hom he).symm.trans hi
    exact (congrArg x.ofConv he').trans
      (congrArg (fun z : WithConv (A →ₐ[K] K) => z.ofConv a) hx)
  · rintro ⟨x, rfl⟩
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro a ha
    have hz := (HopfIdeal.mem_kerOfSurjective f.hom hf).mp ha
    exact (congrArg x.ofConv hz).trans (map_zero x.ofConv)

private abbrev pIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (standardParabolicPoints G I)
private abbrev rIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
    (parabolicRadicalRoots_closed G.rootBase I)

private theorem parabolicReduced (I : Set G.rootBase.support) :
    IsReduced (parabolicAlgebra G I) := by
  change IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj (pIdeal G I))
  infer_instance
private theorem parabolicFinite (I : Set G.rootBase.support) :
    Algebra.FiniteType K (parabolicAlgebra G I) := by
  change Algebra.FiniteType K (G.coordinateAlgebra ⧸ (pIdeal G I).toIdeal)
  infer_instance
attribute [local instance] parabolicReduced parabolicFinite

private theorem rootReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (rIdeal G I).toIdeal) := by
  change IsReduced (G.rootSubsetAlgebra _ _)
  infer_instance
attribute [local instance] rootReduced

private theorem parabolic_le_root (I : Set G.rootBase.support) : pIdeal G I ≤ rIdeal G I := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  intro r hr
  apply ((HopfIdeal.le_vanishingIdeal_iff _ (pIdeal G I)).mp le_rfl)
  rw [parabolic_eq_levi_sup_unipotent]
  exact (show parabolicUnipotentPoints G I ≤ _ from le_sup_right) hr

private abbrev rootMap (I : Set G.rootBase.support) :
    (parabolicAlgebra G I).obj ⟶
      (G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
        (parabolicRadicalRoots_closed G.rootBase I)).obj :=
  CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj (parabolic_le_root G I)

private theorem rootMap_surjective (I : Set G.rootBase.support) :
    Function.Surjective (rootMap G I).hom :=
  CommHopfAlgCat.quotientMapOfLe_surjective G.coordinateAlgebra.obj _

/-- The defining Hopf ideal of the outside-subsystem root group inside the parabolic. -/
def parabolicUnipotentIdeal (I : Set G.rootBase.support) : HopfIdeal K (parabolicAlgebra G I) :=
  HopfIdeal.kerOfSurjective (rootMap G I).hom (rootMap_surjective G I)

/-- The root-factor quotient of the parabolic coordinate algebra is its root-group algebra. -/
def parabolicUnipotentQuotientIso (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotient (parabolicAlgebra G I).obj (parabolicUnipotentIdeal G I) ≅
      (G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
        (parabolicRadicalRoots_closed G.rootBase I)).obj :=
  CommHopfAlgCat.quotientKerOfSurjectiveIso (rootMap G I) (rootMap_surjective G I)

/-- The root-factor quotient is reduced. -/
instance parabolicUnipotentIdeal_reduced (I : Set G.rootBase.support) :
    IsReduced ((parabolicAlgebra G I) ⧸ (parabolicUnipotentIdeal G I).toIdeal) :=
  HopfIdeal.isReduced_quotient_kerOfSurjective (rootMap G I).hom (rootMap_surjective G I)

private abbrev qP (I : Set G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] parabolicAlgebra G I :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (pIdeal G I)).hom
private abbrev qR (I : Set G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] G.rootSubsetAlgebra
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I) :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (rIdeal G I)).hom

private theorem rootMap_comp (I : Set G.rootBase.support) :
    (rootMap G I).hom.comp (qP G I) = qR G I := by
  ext a
  exact CommHopfAlgCat.quotientMapOfLe_mk G.coordinateAlgebra.obj (parabolic_le_root G I) a

private theorem point_comp (I : Set G.rootBase.support)
    (x : WithConv ((G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I)) →ₐ[K] K)) :
    AlgHom.mapDomain (qP G I) (AlgHom.mapDomain (rootMap G I).hom x) =
      AlgHom.mapDomain (qR G I) x := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  exact congrArg x.ofConv (congrArg (fun f : G.coordinateAlgebra →ₐc[K]
    G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I) => f a) (rootMap_comp G I))

omit [IsAlgClosed K] [CharZero K] in
private theorem mapDomain_injective {A B : Type u} [CommRing A] [CommRing B]
    [HopfAlgebra K A] [HopfAlgebra K B] (f : A →ₐc[K] B) (hf : Function.Surjective f) :
    Function.Injective (AlgHom.mapDomain (A := K) f) := by
  intro g h he
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, ha⟩ := hf b
  have hv := congrArg (fun p : WithConv (A →ₐ[K] K) => p.ofConv a) he
  change g.ofConv (f a) = h.ofConv (f a) at hv
  exact (congrArg g.ofConv ha).symm.trans (hv.trans (congrArg h.ofConv ha))

/-- The root-factor ideal cuts out the prescribed subgroup on parabolic coordinates. -/
theorem parabolicUnipotentIdeal_points (I : Set G.rootBase.support)
    (g : WithConv ((parabolicAlgebra G I) →ₐ[K] K)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (parabolicAlgebra G I).obj
      (parabolicUnipotentIdeal G I) (CommAlgCat.of K K) ↔
        AlgHom.mapDomain (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj
          (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))).hom g ∈
            parabolicUnipotentPoints G I := by
  unfold parabolicUnipotentIdeal
  rw [kernel_points_range (rootMap G I) (rootMap_surjective G I)]
  constructor
  · rintro ⟨x, rfl⟩
    rw [point_comp]
    exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
      G.coordinateAlgebra.obj (rIdeal G I) (CommAlgCat.of K K) x
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hf : Function.Surjective (qP G I) :=
      CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj (pIdeal G I)
    apply mapDomain_injective (qP G I) hf
    exact (point_comp G I x).trans hx

private theorem parabolicPoint_coe (I : Set G.rootBase.support)
    (g : WithConv ((parabolicAlgebra G I) →ₐ[K] K)) :
    (parabolicPointsMulEquiv G I (affineGroupPointsMulEquiv K (parabolicAlgebra G I) g) :
      G.points) = AlgHom.mapDomain (qP G I) g := by
  change CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj (pIdeal G I)
      (CommAlgCat.of K K) ((affineGroupPointsMulEquiv K (parabolicAlgebra G I)).symm
        (affineGroupPointsMulEquiv K (parabolicAlgebra G I) g)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem parabolicPoint_mem (I : Set G.rootBase.support)
    (g : WithConv ((parabolicAlgebra G I) →ₐ[K] K)) :
    AlgHom.mapDomain (qP G I) g ∈ standardParabolicPoints G I := by
  rw [← parabolicPoint_coe]
  exact (parabolicPointsMulEquiv G I
    (affineGroupPointsMulEquiv K (parabolicAlgebra G I) g)).property

/-- The outside-subsystem root group is a normal closed subgroup of the parabolic. -/
theorem parabolicUnipotentIdeal_isNormal (I : Set G.rootBase.support) :
    (parabolicUnipotentIdeal G I).IsNormal := by
  apply normal_of_points
  constructor
  intro n hn g
  rw [parabolicUnipotentIdeal_points] at hn ⊢
  let np : standardParabolicPoints G I := ⟨AlgHom.mapDomain (qP G I) n,
    parabolicPoint_mem G I n⟩
  let gp : standardParabolicPoints G I := ⟨AlgHom.mapDomain (qP G I) g,
    parabolicPoint_mem G I g⟩
  have hnp : np ∈ (parabolicUnipotentPoints G I).subgroupOf (standardParabolicPoints G I) := hn
  have hc := (parabolicUnipotent_normal G I).conj_mem np hnp gp
  change AlgHom.mapDomain (qP G I) g * AlgHom.mapDomain (qP G I) n *
    (AlgHom.mapDomain (qP G I) g)⁻¹ ∈ parabolicUnipotentPoints G I at hc
  simpa only [map_mul, map_inv] using hc

/-- The root-factor quotient is geometrically connected. -/
theorem parabolicUnipotent_connected (I : Set G.rootBase.support) :
    geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I)
        (parabolicUnipotentIdeal G I)).obj :=
  (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso
    (parabolicUnipotentQuotientIso G I).symm
    (G.rootSubset_geometricallyConnected _ (parabolicRadicalRoots_closed G.rootBase I))

/-- The root-factor quotient is smooth and geometrically unipotent. -/
theorem parabolicUnipotent_smoothUnipotent (I : Set G.rootBase.support) :
    smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I)
        (parabolicUnipotentIdeal G I)) := by
  have hr := (smoothUnipotentCommHopfAlgProperty_iff K _).mp
    (G.rootSubset_smoothUnipotent _ (parabolicRadicalRoots_closed G.rootBase I))
  have hs := (smoothCommHopfAlgProperty K).prop_of_iso (parabolicUnipotentQuotientIso G I).symm
    ((smoothCommHopfAlgProperty_iff _).mpr hr.1)
  have hu := (geometricallyUnipotentPointsCommHopfAlgProperty K).prop_of_iso
    (parabolicUnipotentQuotientIso G I).symm
    ((geometricallyUnipotentPointsCommHopfAlgProperty_iff K _).mpr hr.2)
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact ⟨(smoothCommHopfAlgProperty_iff _).mp hs,
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff K _).mp hu⟩

end SchubertGeometry
