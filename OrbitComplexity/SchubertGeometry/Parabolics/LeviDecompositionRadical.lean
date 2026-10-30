import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionRadicalIdeal
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionHopf
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Properties
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-! # Unipotent radicals of standard parabolics

Normal connected smooth unipotent subgroups have trivial Levi image. The computed
projection kernel places all of them in the complementary positive-root subgroup,
which therefore equals the canonical unipotent radical.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
attribute [local irreducible] parabolicLeviProjection parabolicProjectionMap

/-- A normal connected smooth unipotent subgroup has trivial image in the Levi factor. -/
theorem parabolicUnipotent_image_trivial (I : Set G.rootBase.support)
    (J : HopfIdeal K (parabolicAlgebra G I))
    (hJ : HopfIdeal.IsUnipotentRadicalCandidate (parabolicAlgebra G I) J) :
    HopfIdeal.ker ((parabolicProjectionMap G I) ≫
      CommHopfAlgCat.mkQuotient (parabolicAlgebra G I).obj J).hom =
        HopfIdeal.augmentation K (G.leviAlgebra I) := by
  let g : (G.leviAlgebra I).obj ⟶
      (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I) J).obj :=
    parabolicProjectionMap G I ≫ CommHopfAlgCat.mkQuotient (parabolicAlgebra G I).obj J
  have hker : HopfIdeal.ker g.hom = J.comap (parabolicProjectionMap G I).hom := by
    ext x
    rw [HopfIdeal.mem_ker, HopfIdeal.mem_comap]
    change (CommHopfAlgCat.mkQuotient (parabolicAlgebra G I).obj J).hom
      ((parabolicProjectionMap G I).hom x) = 0 ↔ _
    exact CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _
  have hnormal : (HopfIdeal.ker g.hom).IsNormal := by
    rw [hker]
    exact hJ.isNormal.comap_of_injective _ (parabolicProjectionMap_injective G I)
  have hconnected : geometricallyConnectedCommHopfAlgProperty K (CommHopfAlgCat.image g) :=
    geometricallyConnectedCommHopfAlgProperty.image g hJ.geometricallyConnected
  have hsource := (smoothUnipotentCommHopfAlgProperty_iff K _).mp hJ.smoothUnipotent
  have hsmooth : smoothCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I) J).obj :=
    (smoothCommHopfAlgProperty_iff _).mpr hsource.1
  let _ : Algebra.Smooth K (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I) J) :=
    hsource.1
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I) J) :=
    isReduced_of_smooth K _
  have hu : geometricallyUnipotentPointsCommHopfAlgProperty K (CommHopfAlgCat.image g) :=
    geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced g
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff K _).mpr hsource.2)
  have hs : smoothCommHopfAlgProperty K (CommHopfAlgCat.image g) :=
    smoothCommHopfAlgProperty.image g hsmooth
  have hsu : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) (HopfIdeal.ker g.hom)) := by
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    exact ⟨(smoothCommHopfAlgProperty_iff _).mp hs,
      (geometricallyUnipotentPointsCommHopfAlgProperty_iff K _).mp hu⟩
  exact levi_unipotent_eq_augmentation G I (HopfIdeal.ker g.hom) hnormal hconnected hsu

private theorem parabolicReduced (I : Set G.rootBase.support) :
    IsReduced (parabolicAlgebra G I) := by
  change IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)))
  infer_instance
private theorem parabolicFinite (I : Set G.rootBase.support) :
    Algebra.FiniteType K (parabolicAlgebra G I) := by
  change Algebra.FiniteType K (G.coordinateAlgebra ⧸
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)).toIdeal)
  infer_instance
attribute [local instance] parabolicReduced parabolicFinite

omit [IsAlgClosed K] [CharZero K] in
private theorem hopf_points {A B : _root_.CommHopfAlgCat.{u} K}
    [IsReduced A] [IsReduced B] [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (f : A ⟶ B) (p : WithConv (B →ₐ[K] K)) :
    Variety.mapPoints (X := affineVariety K B) (Y := affineVariety K A)
      ((hopfSpec (CommRingCat.of K)).map f.op).hom.hom
      (affineGroupPointsMulEquiv K B p) =
        affineGroupPointsMulEquiv K A (AlgHom.mapDomain f.hom p) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom (p.ofConv.comp f.hom.toAlgHom).toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem parabolicPoint_coe (I : Set G.rootBase.support)
    (g : WithConv ((parabolicAlgebra G I) →ₐ[K] K)) :
    (parabolicPointsMulEquiv G I (affineGroupPointsMulEquiv K (parabolicAlgebra G I) g) :
      G.points) = AlgHom.mapDomain
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj
          (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))).hom g := by
  change CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj
      (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))
      (CommAlgCat.of K K) ((affineGroupPointsMulEquiv K (parabolicAlgebra G I)).symm
        (affineGroupPointsMulEquiv K (parabolicAlgebra G I) g)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Every connected normal smooth unipotent subgroup lies in the parabolic root factor. -/
theorem parabolicUnipotentIdeal_le (I : Set G.rootBase.support)
    (J : HopfIdeal K (parabolicAlgebra G I))
    (hJ : HopfIdeal.IsUnipotentRadicalCandidate (parabolicAlgebra G I) J) :
    parabolicUnipotentIdeal G I ≤ J := by
  have hs := (smoothUnipotentCommHopfAlgProperty_iff K _).mp hJ.smoothUnipotent
  let _ : Algebra.Smooth K (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I) J) := hs.1
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient (parabolicAlgebra G I) J) :=
    isReduced_of_smooth K _
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  intro g hg
  apply (parabolicUnipotentIdeal_points G I g).mpr
  have hi := parabolicUnipotent_image_trivial G I J hJ
  let l : WithConv ((G.leviAlgebra I) →ₐ[K] K) :=
    AlgHom.mapDomain (parabolicProjectionMap G I).hom g
  have hl : l ∈ CommHopfAlgCat.quotientPointsSubgroup (G.leviAlgebra I).obj
      (HopfIdeal.augmentation K (G.leviAlgebra I)) (CommAlgCat.of K K) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro a ha
    have ha' : a ∈ HopfIdeal.ker ((parabolicProjectionMap G I) ≫
        CommHopfAlgCat.mkQuotient (parabolicAlgebra G I).obj J).hom := hi.symm ▸ ha
    have hmem : (parabolicProjectionMap G I).hom a ∈ J := by
      apply (CommHopfAlgCat.mkQuotient_eq_zero_iff (parabolicAlgebra G I).obj J _).mp
      exact (HopfIdeal.mem_ker _).mp ha'
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff (parabolicAlgebra G I).obj J
      (CommAlgCat.of K K) g).mp hg _ hmem
  have hlone : l = 1 :=
    CommHopfAlgCat.eq_one_of_mem_quotientPointsSubgroup_augmentation _ _ hl
  let p := affineGroupPointsMulEquiv K (parabolicAlgebra G I) g
  have hp : Variety.mapPoints (parabolicLeviProjection G I) p = 1 := by
    have hc := congrArg (fun f : (standardParabolicVariety G I).toOver ⟶
        (leviVariety G I).toOver => Variety.mapPoints
          (X := standardParabolicVariety G I) (Y := leviVariety G I) f p)
      (parabolicProjectionMap_spec G I)
    have ht := hopf_points (parabolicProjectionMap G I) g
    exact hc.symm.trans (ht.trans
      ((congrArg (affineGroupPointsMulEquiv K (G.leviAlgebra I)) hlone).trans (map_one _)))
  have hu := (parabolicLeviProjection_kernel G I p).mp hp
  exact (parabolicPoint_coe G I g) ▸ hu

/-- The root factor is a connected normal smooth unipotent subgroup of the parabolic. -/
theorem parabolicUnipotent_isCandidate (I : Set G.rootBase.support) :
    HopfIdeal.IsUnipotentRadicalCandidate (parabolicAlgebra G I)
      (parabolicUnipotentIdeal G I) :=
  ⟨parabolicUnipotentIdeal_isNormal G I, parabolicUnipotent_connected G I,
    parabolicUnipotent_smoothUnipotent G I⟩

/-- The positive roots outside the Levi subsystem define the parabolic's unipotent radical. -/
theorem parabolicUnipotent_isRadical (I : Set G.rootBase.support) :
    parabolicUnipotentIdeal G I =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (parabolicAlgebra G I) :=
  (FiniteTypeCommHopfAlgCat.eq_unipotentRadicalDefiningIdeal_iff _ _).mpr
    ⟨parabolicUnipotent_isCandidate G I, parabolicUnipotentIdeal_le G I⟩

end SchubertGeometry
