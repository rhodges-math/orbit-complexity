import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionProjection
import OrbitComplexity.SchubertGeometry.Parabolics.BorelInclusion
import OrbitComplexity.SchubertGeometry.Levi.BorelInclusion

/-! # The Borel projection into a singleton Levi Borel -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
universe u
variable {K : Type u} [Field K]

private def factorOver {A B C : Variety K} (f : A.toOver ⟶ C.toOver)
    (i : B.toOver ⟶ C.toOver) [IsPreimmersion i.left]
    (hr : Set.range (f.left : A.scheme → C.scheme) ⊆ Set.range (i.left : B.scheme → C.scheme)) :
    A.toOver ⟶ B.toOver := by
  have : IsReduced A.toOver.left := A.reduced
  exact Over.homMk (liftPreimmersion i.left f.left hr) (by
    have hi : i.left ≫ C.toSpec = B.toSpec := i.w
    change liftPreimmersion i.left f.left hr ≫ B.toSpec = A.toSpec
    rw [← hi, ← Category.assoc, liftPreimmersion_fac]
    exact f.w)

private theorem factorOver_comp {A B C : Variety K} (f : A.toOver ⟶ C.toOver)
    (i : B.toOver ⟶ C.toOver) [IsPreimmersion i.left]
    (hr : Set.range (f.left : A.scheme → C.scheme) ⊆ Set.range (i.left : B.scheme → C.scheme)) :
    factorOver f i hr ≫ i = f := by
  have : IsReduced A.toOver.left := A.reduced
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac i.left f.left hr

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def projectedBorel (I : Set G.rootBase.support) :
    (borelVariety G).toOver ⟶ (leviVariety G I).toOver :=
  borelParabolicInclusion G I ≫ parabolicLeviProjection G I

private theorem projectedBorel_image (I : Set G.rootBase.support) :
    Set.range (Variety.mapPoints (projectedBorel G I)) ⊆
      Set.range (Variety.mapPoints (leviBorelLeviInclusion G I)) := by
  rintro _ ⟨b, rfl⟩
  let p := Variety.mapPoints (borelParabolicInclusion G I) b
  let gp := parabolicPointsMulEquiv G I p
  obtain ⟨x, ⟨hl, hr, hx⟩, _⟩ := parabolic_existsUnique_levi_mul G I gp.val gp.property
  have hgb : (gp : G.points) = (borelPointsMulEquiv G b : G.points) :=
    borelParabolic_points G I b
  have hrB : x.2 ∈ G.borelPoints :=
    G.unipotent_le_borel (G.rootSubsetPoints_le_unipotent _ _ hr)
  have hlB : x.1 ∈ G.borelPoints := by
    have he : x.1 = (gp : G.points) * x.2⁻¹ := by rw [← hx]; group
    rw [he, hgb]
    exact G.borelPoints.mul_mem (borelPointsMulEquiv G b).property
      (G.borelPoints.inv_mem hrB)
  let l : G.leviPoints I := ⟨x.1, hl⟩
  let r : parabolicUnipotentPoints G I := ⟨x.2, hr⟩
  have hf : parabolicPointProjection G I gp = l :=
    parabolicPointProjection_factors G I gp l r hx
  let t : (leviBorelVariety G I).points :=
    (leviBorelPointsMulEquiv G I).symm ⟨x.1, hl, hlB⟩
  refine ⟨t, ?_⟩
  change Variety.mapPoints (leviBorelLeviInclusion G I) t =
    Variety.mapPoints (borelParabolicInclusion G I ≫ parabolicLeviProjection G I) b
  rw [Variety.mapPoints_comp]
  apply (leviPointsMulEquiv G I).injective
  apply Subtype.ext
  change (leviPointsMulEquiv G I
      (Variety.mapPoints (leviBorelLeviInclusion G I) t) : G.points) =
    (leviPointsMulEquiv G I (Variety.mapPoints (parabolicLeviProjection G I) p) : G.points)
  calc
    _ = (leviBorelPointsMulEquiv G I t : G.points) :=
      leviBorelLeviInclusion_points G I t
    _ = x.1 := congrArg Subtype.val ((leviBorelPointsMulEquiv G I).apply_symm_apply _)
    _ = (parabolicPointProjection G I gp : G.points) :=
      (congrArg Subtype.val hf).symm
    _ = _ := congrArg Subtype.val (parabolicLeviProjection_points G I p).symm

/-- The regular Borel projection to the Borel of the singleton Levi. -/
@[irreducible] def simpleBorelProjection (i : G.rootBase.support) :
    (borelVariety G).toOver ⟶ (leviBorelVariety G {i}).toOver :=
  factorOver (projectedBorel G {i}) (leviBorelLeviInclusion G {i})
    (Variety.range_subset_of_mapPoints _ _ (projectedBorel_image G {i}))

/-- The singleton Borel projection agrees with the parabolic Levi projection. -/
theorem simpleBorelProjection_comp (i : G.rootBase.support) :
    simpleBorelProjection G i ≫ leviBorelLeviInclusion G {i} =
      borelParabolicInclusion G {i} ≫ parabolicLeviProjection G {i} := by
  unfold simpleBorelProjection
  exact factorOver_comp _ _ _

end SchubertGeometry
