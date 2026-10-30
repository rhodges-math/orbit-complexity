import OrbitComplexity.SchubertGeometry.Levi.Maps
import OrbitComplexity.GroupActions.Varieties.BijectivePoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFactors

/-! # Dimension of Levi--Borel groups

Multiplication from the chosen torus and positive Levi root subgroup is bijective
on rational points. Its source is integral, so the dimension formula gives the
sum of the two factor dimensions.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The product of the chosen torus with the positive Levi root subgroup. -/
abbrev leviBorelProduct (I : Set G.rootBase.support) : Variety K :=
  Variety.productVariety (torusVariety G) (rootSubsetVariety G
    (leviPositiveRoots G.rootBase I) (LeviRootSpan.isPositiveRootClosed G.rootBase I))

/-- Multiplication from the torus and positive Levi roots into the Levi--Borel group. -/
def leviBorelMultiplication (I : Set G.rootBase.support) :
    (leviBorelProduct G I).toOver ⟶ (leviBorelVariety G I).toOver :=
  (fst _ _ ≫ torusLeviBorelInclusion G I) * (snd _ _ ≫ leviRootBorelInclusion G I)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

/-- Torus--root multiplication on rational points is multiplication in the ambient group. -/
theorem leviBorelMultiplication_points (I : Set G.rootBase.support)
    (p : (leviBorelProduct G I).points) :
    (leviBorelPointsMulEquiv G I (Variety.mapPoints (leviBorelMultiplication G I) p) :
        G.points) =
      (torusPointsMulEquiv G (Variety.mapPoints (fst _ _) p) : G.points) *
        (rootSubsetPointsMulEquiv G _ (LeviRootSpan.isPositiveRootClosed G.rootBase I)
          (Variety.mapPoints (snd _ _) p) : G.points) := by
  rw [leviBorelMultiplication, mapPoints_mul, Variety.mapPoints_comp,
    Variety.mapPoints_comp, map_mul]
  change _ * _ = _ * _
  rw [torusLeviBorelInclusion_points, leviRootBorelInclusion_points]

private def pairPoint (I : Set G.rootBase.support) (t : (torusVariety G).points)
    (u : (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).points) :
    (leviBorelProduct G I).points :=
  (leviBorelProduct G I).pointsEquivOverHom.symm
    (lift ((torusVariety G).pointsEquivOverHom t)
      ((rootSubsetVariety G _ _).pointsEquivOverHom u))

private theorem pairPoint_fst (I : Set G.rootBase.support) (t : (torusVariety G).points)
    (u : (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).points) :
    Variety.mapPoints (fst _ _) (pairPoint G I t u) = t := by
  apply (torusVariety G).pointsEquivOverHom.injective
  change (leviBorelProduct G I).pointsEquivOverHom (pairPoint G I t u) ≫ fst _ _ = _
  rw [pairPoint, Equiv.apply_symm_apply, lift_fst]

private theorem pairPoint_snd (I : Set G.rootBase.support) (t : (torusVariety G).points)
    (u : (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).points) :
    Variety.mapPoints (snd _ _) (pairPoint G I t u) = u := by
  apply (rootSubsetVariety G _ _).pointsEquivOverHom.injective
  change (leviBorelProduct G I).pointsEquivOverHom (pairPoint G I t u) ≫ snd _ _ = _
  rw [pairPoint, Equiv.apply_symm_apply, lift_snd]

private theorem torus_unipotent_unique (t₁ t₂ u₁ u₂ : G.points)
    (ht₁ : t₁ ∈ G.torusPoints) (ht₂ : t₂ ∈ G.torusPoints)
    (hu₁ : u₁ ∈ G.unipotentPoints) (hu₂ : u₂ ∈ G.unipotentPoints)
    (he : t₁ * u₁ = t₂ * u₂) : t₁ = t₂ ∧ u₁ = u₂ := by
  have hgu : t₂⁻¹ * t₁ = u₂ * u₁⁻¹ := by
    calc
      t₂⁻¹ * t₁ = t₂⁻¹ * (t₁ * u₁) * u₁⁻¹ := by group
      _ = t₂⁻¹ * (t₂ * u₂) * u₁⁻¹ := by rw [he]
      _ = u₂ * u₁⁻¹ := by group
  have hT : t₂⁻¹ * t₁ ∈ G.torusPoints :=
    G.torusPoints.mul_mem (G.torusPoints.inv_mem ht₂) ht₁
  have hU : t₂⁻¹ * t₁ ∈ G.unipotentPoints := hgu ▸
    G.unipotentPoints.mul_mem hu₂ (G.unipotentPoints.inv_mem hu₁)
  have hone := BorelRootUnipotent.torus_intersection_eq_one G.torusIdeal G.borelIdeal
    G.isBorel G.torusSplit G.split_surjective G.split_eq_zero (CommAlgCat.of K K)
    (t₂⁻¹ * t₁) hT hU
  have ht : t₁ = t₂ := (inv_mul_eq_one.mp hone).symm
  refine ⟨ht, ?_⟩
  rw [ht] at he
  exact mul_left_cancel he

private theorem multiplication_injective (I : Set G.rootBase.support) :
    Function.Injective (Variety.mapPoints (leviBorelMultiplication G I)) := by
  intro p q hpq
  let tp : G.torusPoints := torusPointsMulEquiv G (Variety.mapPoints (fst _ _) p)
  let tq : G.torusPoints := torusPointsMulEquiv G (Variety.mapPoints (fst _ _) q)
  let rp : G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) :=
    rootSubsetPointsMulEquiv G _ (LeviRootSpan.isPositiveRootClosed G.rootBase I)
      (Variety.mapPoints (snd _ _) p)
  let rq : G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) :=
    rootSubsetPointsMulEquiv G _ (LeviRootSpan.isPositiveRootClosed G.rootBase I)
      (Variety.mapPoints (snd _ _) q)
  have hm : (tp : G.points) * rp = (tq : G.points) * rq :=
    (leviBorelMultiplication_points G I p).symm.trans
      ((congrArg (fun b => (leviBorelPointsMulEquiv G I b : G.points)) hpq).trans
        (leviBorelMultiplication_points G I q))
  have hrp : (rp : G.points) ∈ G.unipotentPoints :=
    G.rootSubsetPoints_le_unipotent _ _ rp.property
  have hrq : (rq : G.points) ∈ G.unipotentPoints :=
    G.rootSubsetPoints_le_unipotent _ _ rq.property
  have he := torus_unipotent_unique G tp tq rp rq tp.property tq.property hrp hrq hm
  have ht : Variety.mapPoints (fst _ _) p = Variety.mapPoints (fst _ _) q := by
    apply (torusPointsMulEquiv G).injective
    exact Subtype.ext he.1
  have hu : Variety.mapPoints (snd _ _) p = Variety.mapPoints (snd _ _) q := by
    apply (rootSubsetPointsMulEquiv G _
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).injective
    exact Subtype.ext he.2
  apply (leviBorelProduct G I).pointsEquivOverHom.injective
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg (torusVariety G).pointsEquivOverHom ht
  · exact congrArg (rootSubsetVariety G _ _).pointsEquivOverHom hu

private theorem multiplication_surjective (I : Set G.rootBase.support) :
    Function.Surjective (Variety.mapPoints (leviBorelMultiplication G I)) := by
  intro b
  obtain ⟨t, ht, u, hu, htu⟩ := G.leviBorel_exists_torus_mul I
    (leviBorelPointsMulEquiv G I b) (leviBorelPointsMulEquiv G I b).property
  let tp := (torusPointsMulEquiv G).symm ⟨t, ht⟩
  let up := (rootSubsetPointsMulEquiv G _
    (LeviRootSpan.isPositiveRootClosed G.rootBase I)).symm ⟨u, hu⟩
  refine ⟨pairPoint G I tp up, ?_⟩
  apply (leviBorelPointsMulEquiv G I).injective
  apply Subtype.ext
  rw [leviBorelMultiplication_points, pairPoint_fst, pairPoint_snd]
  have htp : (torusPointsMulEquiv G tp : G.points) = t :=
    congrArg Subtype.val ((torusPointsMulEquiv G).apply_symm_apply ⟨t, ht⟩)
  have hup : (rootSubsetPointsMulEquiv G _
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) up : G.points) = u :=
    congrArg Subtype.val ((rootSubsetPointsMulEquiv G _
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).apply_symm_apply ⟨u, hu⟩)
  rw [htp, hup]
  exact htu

/-- Every Levi--Borel point has a unique torus--positive-root factorization. -/
theorem leviBorelMultiplication_bijective (I : Set G.rootBase.support) :
    Function.Bijective (Variety.mapPoints (leviBorelMultiplication G I)) :=
  ⟨multiplication_injective G I, multiplication_surjective G I⟩

/-- The Levi--Borel group has the dimension of its torus plus its positive root subgroup. -/
theorem leviBorelVariety_dim (I : Set G.rootBase.support) :
    (leviBorelVariety G I).dim = (torusVariety G).dim +
      (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I)).dim := by
  have : IsIntegral (leviBorelProduct G I).scheme := Variety.product_integral _ _
  exact (Variety.dim_eq_of_bijective_points (leviBorelMultiplication G I)
    (leviBorelMultiplication_bijective G I)).symm.trans (Variety.productVariety_dim _ _)

end SchubertGeometry
