import OrbitComplexity.SchubertGeometry.FlagVariety.AffineOpen
import OrbitComplexity.GroupActions.Varieties.AffineMulEtale
import OrbitComplexity.GroupActions.Varieties.BijectivePoints
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.GroupActions.Varieties.AffineDimension
import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.RingTheory.Smooth.Regular
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Isomorphisms from subgroup multiplication

A bijective multiplication on rational points is an isomorphism when its identity
differential is injective between smooth groups of the same dimension.
-/

noncomputable section
namespace SchubertGeometry
open GroupActions CategoryTheory AlgebraicGeometry TauCeti
open scoped TensorProduct
universe u
variable {K H A B : Type u} [Field K] [IsAlgClosed K]
  [CommRing H] [HopfAlgebra K H] [Algebra.FiniteType K H] [Algebra.Smooth K H]
  [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Algebra.Smooth K B]
  [IsDomain (A ⊗[K] B)]

omit [IsAlgClosed K] [Algebra.Smooth K A] [Algebra.Smooth K B]
  [IsDomain (A ⊗[K] B)] in
private theorem productFinite : Algebra.FiniteType K (A ⊗[K] B) :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K A)
    (inferInstance : Algebra.FiniteType A (A ⊗[K] B))
omit [IsAlgClosed K] [Algebra.FiniteType K A] [Algebra.FiniteType K B]
  [IsDomain (A ⊗[K] B)] in
private theorem productSmooth : Algebra.Smooth K (A ⊗[K] B) := Algebra.Smooth.comp K A _
attribute [local instance] productFinite productSmooth

private theorem finrank_lie_eq_dim {D : Type u} [CommRing D] [HopfAlgebra K D]
    [Algebra.FiniteType K D] [Algebra.Smooth K D] :
    (Module.finrank K (Derivation K D (TauCeti.Bialgebra.CounitAlgebra K D K)) :
      WithBot ℕ∞) = ringKrullDim D := by
  let : IsRegularRing D := TauCeti.IsRegularRing.of_smooth (R := K)
  apply (TauCeti.HopfAlgebra.isRegularLocalRing_augmentationStalk_iff (k := K)).mp
  infer_instance

omit [IsAlgClosed K] [Algebra.Smooth K H] [Algebra.Smooth K A]
  [Algebra.Smooth K B] in
private theorem affine_points_bijective [IsReduced H] (f : H →ₐ[K] A ⊗[K] B)
    (h : Function.Bijective (fun p : A ⊗[K] B →ₐ[K] K => p.comp f)) :
    Function.Bijective (Variety.mapPoints (affineMorphism f)) := by
  constructor
  · intro x y he
    obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K (A ⊗[K] B)).symm.surjective x
    obtain ⟨q, rfl⟩ := (affineVarietyPointsEquiv K (A ⊗[K] B)).symm.surjective y
    rw [affineMorphism_points, affineMorphism_points] at he
    exact congrArg (affineVarietyPointsEquiv K (A ⊗[K] B)).symm
      (h.1 ((affineVarietyPointsEquiv K H).symm.injective he))
  · intro y
    obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K H).symm.surjective y
    obtain ⟨q, hq⟩ := h.2 p
    refine ⟨(affineVarietyPointsEquiv K (A ⊗[K] B)).symm q, ?_⟩
    rw [affineMorphism_points]
    exact congrArg (affineVarietyPointsEquiv K H).symm hq

omit [IsAlgClosed K] [Algebra.FiniteType K H] [Algebra.Smooth K H]
  [Algebra.FiniteType K A] [Algebra.Smooth K A] [Algebra.FiniteType K B]
  [Algebra.Smooth K B] [IsDomain (A ⊗[K] B)] in
/-- Disjoint injective subgroup tangent images make the multiplication differential injective. -/
theorem affineMulTangent_injective (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : Disjoint (derivationComp (B := K) f).range (derivationComp (B := K) g).range) :
    Function.Injective (affineMulTangent f g) := by
  let F := derivationComp (B := K) f
  let G := derivationComp (B := K) g
  have hk : (F.coprod G).ker = ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range F G h,
      LinearMap.ker_eq_bot.mpr (derivationComp_injective_of_surjective f hf),
      LinearMap.ker_eq_bot.mpr (derivationComp_injective_of_surjective g hg)]
    exact Submodule.prod_bot
  have hi := LinearMap.ker_eq_bot.mp hk
  let e := Derivation.tensorProductLieEquiv (R := K) (B := K) (H₁ := A) (H₂ := B)
  intro x y hxy
  apply e.injective
  apply hi
  have hx := affineMulTangent_prod f g (e x)
  have hy := affineMulTangent_prod f g (e y)
  rw [e.symm_apply_apply] at hx hy
  exact hx.symm.trans (hxy.trans hy)

/-- Smooth subgroup multiplication with injective differential and bijective points is an iso. -/
theorem affineMulMap_isIso (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (hd : Function.Injective (affineMulTangent f g))
    (hp : Function.Bijective (fun p : A ⊗[K] B →ₐ[K] K =>
      p.comp (affineMulMap f.toAlgHom g.toAlgHom))) :
    IsIso (Spec.map (CommRingCat.ofHom
      (affineMulMap f.toAlgHom g.toAlgHom).toRingHom)) := by
  have : IsReduced H := TauCeti.isReduced_of_smooth K H
  have : IsReduced A := TauCeti.isReduced_of_smooth K A
  have : IsReduced B := TauCeti.isReduced_of_smooth K B
  have : IrreducibleSpace (affineVariety K (A ⊗[K] B)).scheme := by
    change IrreducibleSpace (Spec (CommRingCat.of (A ⊗[K] B)))
    infer_instance
  let μ := affineMulMap f.toAlgHom g.toAlgHom
  let φ := affineMorphism μ
  have hp' : Function.Bijective (Variety.mapPoints φ) := affine_points_bijective μ hp
  have hdim : ringKrullDim (A ⊗[K] B) = ringKrullDim H := by
    have he := Variety.dim_eq_of_bijective_points φ hp'
    simpa only [dim_affineVariety] using he
  have hfin : Module.finrank K
      (Derivation K (A ⊗[K] B) (TauCeti.Bialgebra.CounitAlgebra K (A ⊗[K] B) K)) =
      Module.finrank K (Derivation K H (TauCeti.Bialgebra.CounitAlgebra K H K)) := by
    have he := (finrank_lie_eq_dim (K := K) (D := A ⊗[K] B)).trans
      (hdim.trans (finrank_lie_eq_dim (K := K) (D := H)).symm)
    exact_mod_cast he
  have hbij : Function.Bijective (affineMulTangent f g) :=
    ⟨hd, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hd⟩
  have he : μ.toRingHom.Etale := affineMulMap_etale f g hbij
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom μ.toRingHom)) :=
    affineOpenImmersion_of_points μ he hp.1
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  have hr : Set.range (φ.left : _ → _) = Set.univ := by
    have hc := Variety.range_subset_of_mapPoints (𝟙 (affineVariety K H).toOver) φ (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hp'.2 (Variety.mapPoints (𝟙 (affineVariety K H).toOver) y)
      exact ⟨x, hx⟩)
    apply Set.eq_univ_of_forall
    intro y
    exact hc ⟨y, rfl⟩
  exact hr

end SchubertGeometry
