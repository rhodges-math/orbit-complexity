import OrbitComplexity.SchubertGeometry.Roots.BorelRadicals
import OrbitComplexity.SchubertGeometry.Levi.Reductive
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import Mathlib.Tactic

/-! # Intrinsic unipotence in a Levi Borel -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory TauCeti ReductiveGroups SchubertGeometry WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem borelPoint_unipotent_iff (g : G.points) (hg : g ∈ G.borelPoints) :
    g ∈ G.unipotentPoints ↔ HopfAlgebra.IsUnipotentPoint g := by
  classical
  constructor
  · rintro ⟨q, rfl⟩
    have hU : smoothUnipotentCommHopfAlgProperty K G.unipotentAlgebra :=
      (smoothUnipotentCommHopfAlgProperty_iff K G.unipotentAlgebra).mpr
        ⟨G.unipotent_smooth, G.unipotent_geometricallyUnipotent⟩
    exact (smoothUnipotentCommHopfAlgProperty.isUnipotentPoint hU q).mapDomain
      (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.unipotentIdeal).hom
  · intro h
    obtain ⟨V, n, b, hρ⟩ :=
      Comodule.exists_coordinateBialgHom_surjective (k := K) (H := G.coordinateAlgebra)
    let : Module.Finite K V := Module.Finite.of_basis b
    apply (BorelPoint.borelRootUnipotent_iff_matrix_unipotent G.torusIdeal G.borelIdeal
      G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
      G.split_eq_zero G.reductive n (Comodule.coordinateBialgHom b) hρ g hg).mpr
    have hn : IsNilpotent (Comodule.endOfPoint V g.ofConv - 1) :=
      (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
        h (FGComoduleCat.of (R := K) (C := G.coordinateAlgebra) V)
    have hm := hn.map (LinearMap.toMatrixAlgEquiv (b.baseChange K))
    change IsNilpotent ((GeneralLinear.pointsMulEquiv n
      (toConv (g.ofConv.comp (Comodule.coordinateBialgHom b).toAlgHom)) :
        Matrix (Fin n) (Fin n) K) - 1)
    rw [AlgHom.pointsMulEquiv_comp_coordinateBialgHom]
    change IsNilpotent (LinearMap.toMatrix (b.baseChange K) (b.baseChange K)
      (Comodule.endOfPoint V g.ofConv - 1)) at hm
    rw [map_sub (LinearMap.toMatrix (b.baseChange K) (b.baseChange K))
      (Comodule.endOfPoint V g.ofConv) 1, LinearMap.toMatrix_one,
      Comodule.toMatrix_endOfPoint] at hm
    exact hm

private abbrev leviPointMap (I : Set G.rootBase.support) :
    (leviGroupData G I).points →* G.points :=
  AlgHom.mapDomain
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom

private theorem leviBorelIdeal_map (I : Set G.rootBase.support) :
    leviBorelIdealInLevi G I = (G.leviBorelIdeal I).map
      (Bialgebra.Quotient.mkBialgHom (G.leviIdeal I).toIdeal) :=
  CommHopfAlgCat.kerOfSurjective_quotientMapOfLe G.coordinateAlgebra.obj
    (G.leviIdeal_le_leviBorel I)

private theorem leviPointMap_borel (I : Set G.rootBase.support)
    (l : (leviGroupData G I).points) :
    l ∈ (leviGroupData G I).borelPoints ↔ leviPointMap G I l ∈ G.leviBorelPoints I := by
  change l ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K (G.leviAlgebra I))
    (leviBorelIdealInLevi G I) (CommAlgCat.of K K) ↔ _
  rw [leviBorelIdeal_map]
  rw [← G.leviBorelIdeal_points I]
  let q : G.coordinateAlgebra →ₐc[K] G.leviAlgebra I :=
    Bialgebra.Quotient.mkBialgHom (G.leviIdeal I).toIdeal
  have h := CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff_of_surjective
    (CommHopfAlgCat.ofHom q)
    (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj (G.leviIdeal I))
    (G.leviBorelIdeal I) (CommAlgCat.of K K) l
  exact h

private theorem leviUnipotent_image (I : Set G.rootBase.support) :
    ((leviGroupData G I).unipotentPoints).map (leviPointMap G I) =
      G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
  ext g
  rw [← G.levi_unipotent_eq I]
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hlB := (leviGroupData G I).unipotent_le_borel hl
    have hB := (leviPointMap_borel G I l).mp hlB
    refine ⟨hB.1, (borelPoint_unipotent_iff G _ hB.2).mpr ?_⟩
    exact ((borelPoint_unipotent_iff (leviGroupData G I) l hlB).mp hl).mapDomain
      (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom
  · intro hg
    have hgL : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
        (G.leviIdeal I) (CommAlgCat.of K K) := by
      rw [G.leviIdeal_points]
      exact hg.1
    obtain ⟨l, rfl⟩ := hgL
    have hlB := (leviPointMap_borel G I l).mpr
      ⟨hg.1, G.unipotent_le_borel hg.2⟩
    refine ⟨l, (borelPoint_unipotent_iff (leviGroupData G I) l hlB).mpr ?_, rfl⟩
    exact (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective
      (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom
      (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj (G.leviIdeal I)) l).mp
        ((borelPoint_unipotent_iff G _ (G.unipotent_le_borel hg.2)).mp hg.2)

omit [IsAlgClosed K] [CharZero K] in
private theorem points_comap (H L : CommHopfAlgCat.{u} K) (f : H ⟶ L)
    (hf : Function.Surjective f.hom) (J : HopfIdeal K L) :
    CommHopfAlgCat.quotientPointsSubgroup H (J.comapOfSurjective f.hom hf)
        (CommAlgCat.of K K) =
      (CommHopfAlgCat.quotientPointsSubgroup L J (CommAlgCat.of K K)).map
        (AlgHom.mapDomain f.hom) := by
  ext g
  constructor
  · intro hg
    have hv := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hg
    have hk : RingHom.ker f.hom.toAlgHom.toRingHom ≤ RingHom.ker g.ofConv.toRingHom := by
      intro a ha
      change g.ofConv a = 0
      apply hv a
      apply HopfIdeal.mem_comapOfSurjective.mpr
      rw [show f.hom a = 0 from RingHom.mem_ker.mp ha]
      exact J.toIdeal.zero_mem
    let l : WithConv (L →ₐ[K] K) :=
      toConv (AlgHom.liftOfSurjective f.hom.toAlgHom hf g.ofConv hk)
    refine ⟨l, ?_, ?_⟩
    · apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
      intro y hy
      obtain ⟨x, rfl⟩ := hf y
      change AlgHom.liftOfSurjective f.hom.toAlgHom hf g.ofConv hk (f.hom x) = 0
      exact (AlgHom.liftOfSurjective_apply f.hom.toAlgHom hf g.ofConv hk x).trans
        (hv x (HopfIdeal.mem_comapOfSurjective.mpr hy))
    · apply WithConv.ofConv_injective
      exact AlgHom.liftOfSurjective_comp f.hom.toAlgHom hf g.ofConv hk
  · rintro ⟨l, hl, rfl⟩
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
    intro x hx
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hl _
      (HopfIdeal.mem_comapOfSurjective.mp hx)

private theorem leviUnipotent_ideal (I : Set G.rootBase.support) :
    (leviGroupData G I).unipotentIdeal.comapOfSurjective
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom
        (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj (G.leviIdeal I)) =
      G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
  let H := leviGroupData G I
  let q : G.coordinateAlgebra.obj ⟶ CommHopfAlgCat.of K H.coordinateAlgebra :=
    CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)
  have hq : Function.Surjective q.hom :=
    CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj (G.leviIdeal I)
  let J := H.unipotentIdeal.comapOfSurjective q.hom hq
  let e := CommHopfAlgCat.quotientIsoOfSurjective q hq H.unipotentIdeal
  let : IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K H.coordinateAlgebra)
      H.unipotentIdeal) := by
    change IsReduced H.unipotentAlgebra
    let : Algebra.Smooth K H.unipotentAlgebra := H.unipotent_smooth
    exact isReduced_of_smooth K H.unipotentAlgebra
  let : IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj J) :=
    isReduced_of_injective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  let : IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj
      (G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I))) := by
    change IsReduced (G.rootSubsetAlgebra (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I))
    infer_instance
  change J = _
  apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := K)
  change CommHopfAlgCat.quotientPointsSubgroup G.coordinateAlgebra.obj J
    (CommAlgCat.of K K) = _
  rw [points_comap G.coordinateAlgebra.obj (CommHopfAlgCat.of K H.coordinateAlgebra)
    q hq H.unipotentIdeal]
  exact leviUnipotent_image G I

private theorem leviBorelQuotient_apply (I : Set G.rootBase.support)
    (x : G.coordinateAlgebra) :
    (leviBorelQuotientIso G I).hom.hom
        ((CommHopfAlgCat.mkQuotient (G.leviAlgebra I).obj
          (leviBorelIdealInLevi G I)).hom
          ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom x)) =
      (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviBorelIdeal I)).hom x := by
  have hc : CommHopfAlgCat.mkQuotient (G.leviAlgebra I).obj
      (leviBorelIdealInLevi G I) ≫ (leviBorelQuotientIso G I).hom =
        CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
          (G.leviIdeal_le_leviBorel I) :=
    CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _
  have hx := congrArg (fun f : (G.leviAlgebra I).obj ⟶ (G.leviBorelAlgebra I).obj =>
    f.hom ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom x)) hc
  exact hx.trans (CommHopfAlgCat.quotientMapOfLe_mk G.coordinateAlgebra.obj
    (G.leviIdeal_le_leviBorel I) x)

/-- The Levi Borel unipotent radical has exactly the positive Levi-root defining ideal. -/
theorem leviBorelRadical_ambient (I : Set G.rootBase.support) :
    HopfIdeal.comapOfSurjective
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (G.leviBorelAlgebra I))
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviBorelIdeal I)).hom
        (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj _) =
      G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
  let H := leviGroupData G I
  let e : H.borelAlgebra ≅ G.leviBorelAlgebra I :=
    ObjectProperty.isoMk _ (leviBorelQuotientIso G I)
  have hr := FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal e
  rw [← leviUnipotent_ideal G I, ← borelRadical_ambient H]
  ext x
  constructor
  · intro hx
    apply HopfIdeal.mem_comapOfSurjective.mpr
    apply HopfIdeal.mem_comapOfSurjective.mpr
    rw [← hr]
    apply HopfIdeal.mem_comapOfSurjective.mpr
    change (leviBorelQuotientIso G I).hom.hom
      ((CommHopfAlgCat.mkQuotient (G.leviAlgebra I).obj
        (leviBorelIdealInLevi G I)).hom
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom x)) ∈ _
    rw [leviBorelQuotient_apply G I x]
    exact HopfIdeal.mem_comapOfSurjective.mp hx
  · intro hx
    apply HopfIdeal.mem_comapOfSurjective.mpr
    have h1 := HopfIdeal.mem_comapOfSurjective.mp hx
    have h2 := HopfIdeal.mem_comapOfSurjective.mp h1
    rw [← hr] at h2
    have h3 := HopfIdeal.mem_comapOfSurjective.mp h2
    change (leviBorelQuotientIso G I).hom.hom
      ((CommHopfAlgCat.mkQuotient (G.leviAlgebra I).obj
        (leviBorelIdealInLevi G I)).hom
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom x)) ∈ _ at h3
    rw [leviBorelQuotient_apply G I x] at h3
    exact h3

end SchubertGeometry
