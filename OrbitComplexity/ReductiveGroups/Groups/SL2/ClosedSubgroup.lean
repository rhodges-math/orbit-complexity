import OrbitComplexity.ReductiveGroups.Groups.Hopf.SurjectiveBialgebraDescent
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Descent of special-linear morphisms

The two elementary additive subgroups generate the rational points of `SL₂`.
Consequently, their factorizations through a closed subgroup imply that the
whole affine group morphism factors through that subgroup.
-/

noncomputable section

namespace ReductiveGroups

open TauCeti WithConv

universe u v w

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A : Type v} [CommRing A] [HopfAlgebra K A]
  {B : Type w} [CommRing B] [HopfAlgebra K B]

omit [IsAlgClosed K] in
private theorem sl2_points_factor
    (ρ : A →ₐc[K] B)
    (φ : A →ₐc[K] SpecialLinear.coordinateHopfAlgebra K 2)
    (hroot : ∀ (i j : Fin 2) (hij : i ≠ j),
      ∃ x : B →ₐc[K] AdditiveGroup.coordinateHopfAlgebra K,
        x.comp ρ = (SpecialLinear.rootSubgroupCoordinateMap hij).hom.comp φ)
    (q : WithConv (SpecialLinear.coordinateHopfAlgebra K 2 →ₐ[K] K)) :
    AlgHom.mapDomain φ q ∈ (AlgHom.mapDomain (A := K) ρ).range := by
  let P (m : Matrix.SpecialLinearGroup (Fin 2) K) : Prop :=
    AlgHom.mapDomain φ ((SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm m) ∈
      (AlgHom.mapDomain (A := K) ρ).range
  have hP : ∀ m, P m := by
    intro m
    induction m using Matrix.SL2.transvection_induction with
    | htransvec i j hij c =>
      obtain ⟨x, hx⟩ := hroot i j hij
      let t := (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd c)
      refine ⟨AlgHom.mapDomain x t, ?_⟩
      have hq :
          (SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm
              (Matrix.SpecialLinearGroup.transvection hij c) =
            SpecialLinear.rootSubgroupPoints hij t := by
        apply (SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).injective
        simpa only [MulEquiv.apply_symm_apply, t, toAdd_ofAdd] using
          (SpecialLinear.pointsMulEquiv_rootSubgroupPoints (R := K) (A := K) hij t).symm
      change AlgHom.mapDomain ρ (AlgHom.mapDomain x t) =
        AlgHom.mapDomain φ _
      rw [hq]
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro a
      have hxa := congrArg
        (fun f : A →ₐc[K] AdditiveGroup.coordinateHopfAlgebra K => f a) hx
      change t.ofConv (x (ρ a)) =
        (SpecialLinear.rootSubgroupPoints hij t).ofConv (φ a)
      rw [show x (ρ a) =
          (SpecialLinear.rootSubgroupCoordinateMap hij).hom (φ a) from hxa]
      have ht := SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app
        hij (CommAlgCat.of K K) t
      exact congrArg (fun p : WithConv
        (SpecialLinear.coordinateHopfAlgebra K 2 →ₐ[K] K) => p.ofConv (φ a)) ht
    | hmul m n hm hn =>
      simpa only [P, map_mul] using mul_mem hm hn
  simpa only [P, MulEquiv.symm_apply_apply] using
    hP (SpecialLinear.pointsMulEquiv (R := K) (A := K) 2 q)

/-- A morphism from `SL₂` factors uniquely through a closed affine subgroup
when both elementary additive subgroup morphisms factor through it. -/
theorem existsUnique_sl2_factor
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] SpecialLinear.coordinateHopfAlgebra K 2)
    (hroot : ∀ (i j : Fin 2) (hij : i ≠ j),
      ∃ x : B →ₐc[K] AdditiveGroup.coordinateHopfAlgebra K,
        x.comp ρ = (SpecialLinear.rootSubgroupCoordinateMap hij).hom.comp φ) :
    ∃! ψ : B →ₐc[K] SpecialLinear.coordinateHopfAlgebra K 2, ψ.comp ρ = φ := by
  have : IsReduced (SpecialLinear.coordinateHopfAlgebra K 2) :=
    isReduced_of_smooth K _
  have hker (a : A) (ha : ρ a = 0) : φ a = 0 := by
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
    intro q
    obtain ⟨b, hb⟩ := sl2_points_factor ρ φ hroot (toConv q)
    have hba := congrArg (fun p : WithConv (A →ₐ[K] K) => p.ofConv a) hb
    simpa only [TauCeti.AlgHom.mapDomain_apply_apply, ha, map_zero] using hba.symm
  refine ⟨surjectiveBialgebraDescend ρ hρ φ hker,
    surjectiveBialgebraDescend_comp ρ hρ φ hker, ?_⟩
  intro ψ hψ
  exact surjectiveBialgebraDescend_unique ρ hρ φ hker ψ hψ

end ReductiveGroups
