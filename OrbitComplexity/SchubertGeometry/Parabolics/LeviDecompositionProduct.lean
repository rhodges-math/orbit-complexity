import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionMaps
import OrbitComplexity.GroupActions.Varieties.BijectivePoints

/-! # Multiplication of parabolic factors

Levi multiplication with the outside-subsystem root group gives a morphism
whose rational points have unique factors.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem leviIntegral (I : Set G.rootBase.support) :
    IsIntegral (leviVariety G I).scheme := by
  change IsIntegral (reductiveVariety (leviGroupData G I)).scheme
  infer_instance
attribute [local instance] leviIntegral

/-- The product variety of the Levi and the positive roots outside its subsystem. -/
abbrev parabolicLeviProduct (I : Set G.rootBase.support) : Variety K :=
  Variety.productVariety (leviVariety G I) (parabolicUnipotentVariety G I)

/-- Multiplication from the Levi and its complementary positive-root subgroup. -/
def parabolicMultiplication (I : Set G.rootBase.support) :
    (parabolicLeviProduct G I).toOver ⟶ (standardParabolicVariety G I).toOver :=
  (fst _ _ ≫ leviParabolicInclusion G I) * (snd _ _ ≫ parabolicUnipotentInclusion G I)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

/-- Parabolic factor multiplication is the product of the two ambient group points. -/
theorem parabolicMultiplication_points (I : Set G.rootBase.support)
    (p : (parabolicLeviProduct G I).points) :
    (parabolicPointsMulEquiv G I (Variety.mapPoints (parabolicMultiplication G I) p) :
      G.points) =
      (leviPointsMulEquiv G I (Variety.mapPoints (fst _ _) p) : G.points) *
      (rootSubsetPointsMulEquiv G _ (parabolicRadicalRoots_closed G.rootBase I)
        (Variety.mapPoints (snd _ _) p) : G.points) := by
  let f : (parabolicLeviProduct G I).toOver ⟶ (standardParabolicVariety G I).toOver :=
    fst (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver ≫
      leviParabolicInclusion G I
  let g : (parabolicLeviProduct G I).toOver ⟶ (standardParabolicVariety G I).toOver :=
    snd (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver ≫
      parabolicUnipotentInclusion G I
  have hm := mapPoints_mul (X := parabolicLeviProduct G I)
    (H := standardParabolicVariety G I) f g p
  have hf := Variety.mapPoints_comp (X := parabolicLeviProduct G I) (Y := leviVariety G I)
    (Z := standardParabolicVariety G I)
    (fst (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver)
    (leviParabolicInclusion G I) p
  have hg := Variety.mapPoints_comp (X := parabolicLeviProduct G I)
    (Y := parabolicUnipotentVariety G I) (Z := standardParabolicVariety G I)
    (snd (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver)
    (parabolicUnipotentInclusion G I) p
  let eval : (standardParabolicVariety G I).points → G.points := fun q =>
    parabolicPointsMulEquiv G I q
  have hleft := (congrArg eval hf).trans (leviParabolicInclusion_points G I
    (Variety.mapPoints (X := parabolicLeviProduct G I) (Y := leviVariety G I) (fst _ _) p))
  have hright := (congrArg eval hg).trans (parabolicUnipotentInclusion_points G I
    (Variety.mapPoints (X := parabolicLeviProduct G I)
      (Y := parabolicUnipotentVariety G I) (snd _ _) p))
  have hmul : eval (Variety.mapPoints f p * Variety.mapPoints g p) =
      eval (Variety.mapPoints f p) * eval (Variety.mapPoints g p) :=
    congrArg Subtype.val (map_mul (parabolicPointsMulEquiv G I) _ _)
  exact (congrArg eval hm).trans (hmul.trans (congrArg₂ (· * ·) hleft hright))

private def pairPoint (I : Set G.rootBase.support) (l : (leviVariety G I).points)
    (r : (parabolicUnipotentVariety G I).points) : (parabolicLeviProduct G I).points :=
  (parabolicLeviProduct G I).pointsEquivOverHom.symm
    (lift ((leviVariety G I).pointsEquivOverHom l)
      ((parabolicUnipotentVariety G I).pointsEquivOverHom r))

private theorem pairPoint_fst (I : Set G.rootBase.support) (l : (leviVariety G I).points)
    (r : (parabolicUnipotentVariety G I).points) :
    Variety.mapPoints (fst _ _) (pairPoint G I l r) = l := by
  apply (leviVariety G I).pointsEquivOverHom.injective
  change (parabolicLeviProduct G I).pointsEquivOverHom (pairPoint G I l r) ≫ fst _ _ = _
  rw [pairPoint, Equiv.apply_symm_apply, lift_fst]

private theorem pairPoint_snd (I : Set G.rootBase.support) (l : (leviVariety G I).points)
    (r : (parabolicUnipotentVariety G I).points) :
    Variety.mapPoints (snd _ _) (pairPoint G I l r) = r := by
  apply (parabolicUnipotentVariety G I).pointsEquivOverHom.injective
  change (parabolicLeviProduct G I).pointsEquivOverHom (pairPoint G I l r) ≫ snd _ _ = _
  rw [pairPoint, Equiv.apply_symm_apply, lift_snd]

private theorem multiplication_injective (I : Set G.rootBase.support) :
    Function.Injective (Variety.mapPoints (parabolicMultiplication G I)) := by
  intro p q hpq
  let lp := leviPointsMulEquiv G I (Variety.mapPoints (fst _ _) p)
  let lq := leviPointsMulEquiv G I (Variety.mapPoints (fst _ _) q)
  let rp := rootSubsetPointsMulEquiv G _ (parabolicRadicalRoots_closed G.rootBase I)
    (Variety.mapPoints (snd _ _) p)
  let rq := rootSubsetPointsMulEquiv G _ (parabolicRadicalRoots_closed G.rootBase I)
    (Variety.mapPoints (snd _ _) q)
  have hm : (lp : G.points) * rp = (lq : G.points) * rq :=
    (parabolicMultiplication_points G I p).symm.trans
      ((congrArg (fun b => (parabolicPointsMulEquiv G I b : G.points)) hpq).trans
        (parabolicMultiplication_points G I q))
  have he : (lp, rp) = (lq, rq) :=
    Subgroup.mul_injective_of_disjoint (levi_disjoint_parabolicUnipotent G I) hm
  have hl : Variety.mapPoints (fst _ _) p = Variety.mapPoints (fst _ _) q :=
    (leviPointsMulEquiv G I).injective (congrArg Prod.fst he)
  have hr : Variety.mapPoints (snd _ _) p = Variety.mapPoints (snd _ _) q :=
    (rootSubsetPointsMulEquiv G _ (parabolicRadicalRoots_closed G.rootBase I)).injective
      (congrArg Prod.snd he)
  apply (parabolicLeviProduct G I).pointsEquivOverHom.injective
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg (leviVariety G I).pointsEquivOverHom hl
  · exact congrArg (parabolicUnipotentVariety G I).pointsEquivOverHom hr

private theorem multiplication_surjective (I : Set G.rootBase.support) :
    Function.Surjective (Variety.mapPoints (parabolicMultiplication G I)) := by
  intro p
  obtain ⟨q, ⟨hl, hr, he⟩, _⟩ := parabolic_existsUnique_levi_mul G I
    (parabolicPointsMulEquiv G I p) (parabolicPointsMulEquiv G I p).property
  let lp := (leviPointsMulEquiv G I).symm ⟨q.1, hl⟩
  let rp := (rootSubsetPointsMulEquiv G _
    (parabolicRadicalRoots_closed G.rootBase I)).symm ⟨q.2, hr⟩
  refine ⟨pairPoint G I lp rp, ?_⟩
  apply (parabolicPointsMulEquiv G I).injective
  apply Subtype.ext
  have hm := parabolicMultiplication_points G I (pairPoint G I lp rp)
  rw [pairPoint_fst G I lp rp, pairPoint_snd G I lp rp] at hm
  have hlp : (leviPointsMulEquiv G I lp : G.points) = q.1 :=
    congrArg Subtype.val ((leviPointsMulEquiv G I).apply_symm_apply ⟨q.1, hl⟩)
  have hrp : (rootSubsetPointsMulEquiv G _
      (parabolicRadicalRoots_closed G.rootBase I) rp : G.points) = q.2 :=
    congrArg Subtype.val ((rootSubsetPointsMulEquiv G _
      (parabolicRadicalRoots_closed G.rootBase I)).apply_symm_apply ⟨q.2, hr⟩)
  exact hm.trans ((congrArg₂ (· * ·) hlp hrp).trans he)

/-- Parabolic multiplication has a bijective map on rational points. -/
theorem parabolicMultiplication_bijective (I : Set G.rootBase.support) :
    Function.Bijective (Variety.mapPoints (parabolicMultiplication G I)) :=
  ⟨multiplication_injective G I, multiplication_surjective G I⟩

end SchubertGeometry
