import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionVariety
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionGroups
import OrbitComplexity.GroupActions.Actions.MonHomPoints

/-! # Regular projections onto standard Levi subgroups

The inverse product isomorphism gives the regular Levi projection. Unique point factors
identify it with the internal group projection and hence prove multiplicativity.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem iso_hom (I : Set G.rootBase.support) :
    (parabolicLeviIso G I).hom = parabolicMultiplication G I := rfl
attribute [local irreducible] parabolicLeviIso

omit [IsAlgClosed K] [CharZero K] in
private theorem map_inv_right {X Y : Variety K} (e : X.toOver ≅ Y.toOver) (p : Y.points) :
    Variety.mapPoints e.hom (Variety.mapPoints e.inv p) = p := by
  rw [← Variety.mapPoints_comp (X := Y) (Y := X) (Z := Y), e.inv_hom_id,
    Variety.mapPoints_id]

/-- The regular projection of the standard parabolic onto its Levi factor. -/
def parabolicLeviProjection (I : Set G.rootBase.support) :
    (standardParabolicVariety G I).toOver ⟶ (leviVariety G I).toOver :=
  (parabolicLeviIso G I).inv ≫
    fst (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver

attribute [local irreducible] parabolicLeviProjection

/-- On rational points the regular Levi projection is the internal group projection. -/
theorem parabolicLeviProjection_points (I : Set G.rootBase.support)
    (p : (standardParabolicVariety G I).points) :
    leviPointsMulEquiv G I (Variety.mapPoints (parabolicLeviProjection G I) p) =
      parabolicPointProjection G I (parabolicPointsMulEquiv G I p) := by
  let q := Variety.mapPoints (X := standardParabolicVariety G I)
    (Y := parabolicLeviProduct G I) (parabolicLeviIso G I).inv p
  let l := leviPointsMulEquiv G I
    (Variety.mapPoints (X := parabolicLeviProduct G I) (Y := leviVariety G I) (fst _ _) q)
  let r := rootSubsetPointsMulEquiv G _ (parabolicRadicalRoots_closed G.rootBase I)
    (Variety.mapPoints (X := parabolicLeviProduct G I)
      (Y := parabolicUnipotentVariety G I) (snd _ _) q)
  have hm : Variety.mapPoints (X := parabolicLeviProduct G I)
      (Y := standardParabolicVariety G I) (parabolicMultiplication G I) q = p := by
    have h := map_inv_right (X := parabolicLeviProduct G I)
      (Y := standardParabolicVariety G I) (parabolicLeviIso G I) p
    exact (congrArg (fun f : (parabolicLeviProduct G I).toOver ⟶
      (standardParabolicVariety G I).toOver => Variety.mapPoints
        (X := parabolicLeviProduct G I) (Y := standardParabolicVariety G I) f q)
      (iso_hom G I)).symm.trans h
  have hf : (l : G.points) * r = (parabolicPointsMulEquiv G I p : G.points) :=
    (parabolicMultiplication_points G I q).symm.trans
      (congrArg (fun x : (standardParabolicVariety G I).points =>
        (parabolicPointsMulEquiv G I x : G.points)) hm)
  have hgroup := parabolicPointProjection_factors G I (parabolicPointsMulEquiv G I p) l r hf
  have hc := Variety.mapPoints_comp (X := standardParabolicVariety G I)
    (Y := parabolicLeviProduct G I) (Z := leviVariety G I) (parabolicLeviIso G I).inv
    (fst (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver) p
  have hc' : Variety.mapPoints (parabolicLeviProjection G I) p =
      Variety.mapPoints (X := parabolicLeviProduct G I) (Y := leviVariety G I) (fst _ _) q := by
    unfold parabolicLeviProjection
    exact hc
  exact (congrArg (leviPointsMulEquiv G I) hc').trans hgroup.symm

/-- The regular Levi projection preserves the group law. -/
instance parabolicLeviProjection_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (parabolicLeviProjection G I) := by
  apply Variety.isMonHom_of_points (standardParabolicVariety G I) (leviVariety G I)
    (parabolicLeviProjection G I)
  intro x y
  apply (leviPointsMulEquiv G I).injective
  have hxy := parabolicLeviProjection_points G I (x * y)
  have hx := parabolicLeviProjection_points G I x
  have hy := parabolicLeviProjection_points G I y
  calc
    _ = parabolicPointProjection G I (parabolicPointsMulEquiv G I (x * y)) := hxy
    _ = parabolicPointProjection G I (parabolicPointsMulEquiv G I x) *
        parabolicPointProjection G I (parabolicPointsMulEquiv G I y) :=
      (congrArg (parabolicPointProjection G I) (map_mul (parabolicPointsMulEquiv G I) x y)).trans
        (map_mul (parabolicPointProjection G I) _ _)
    _ = leviPointsMulEquiv G I (Variety.mapPoints (parabolicLeviProjection G I) x) *
        leviPointsMulEquiv G I (Variety.mapPoints (parabolicLeviProjection G I) y) :=
      congrArg₂ (· * ·) hx.symm hy.symm
    _ = _ := (map_mul (leviPointsMulEquiv G I) _ _).symm

/-- The Levi inclusion is a section of the regular parabolic projection. -/
@[reassoc]
theorem parabolicLeviProjection_section (I : Set G.rootBase.support) :
    leviParabolicInclusion G I ≫ parabolicLeviProjection G I = 𝟙 (leviVariety G I).toOver := by
  apply Variety.mapPoints_injective (X := leviVariety G I) (Y := leviVariety G I)
  funext l
  apply (leviPointsMulEquiv G I).injective
  let p := Variety.mapPoints (X := leviVariety G I) (Y := standardParabolicVariety G I)
    (leviParabolicInclusion G I) l
  have hinc := leviParabolicInclusion_points G I l
  have he : (leviPointsMulEquiv G I l : G.points) * (1 : parabolicUnipotentPoints G I) =
      (parabolicPointsMulEquiv G I p : G.points) := (mul_one _).trans hinc.symm
  have hgroup := parabolicPointProjection_factors G I (parabolicPointsMulEquiv G I p)
    (leviPointsMulEquiv G I l) 1 he
  have hproj := parabolicLeviProjection_points G I p
  have hc := Variety.mapPoints_comp (X := leviVariety G I) (Y := standardParabolicVariety G I)
    (Z := leviVariety G I) (leviParabolicInclusion G I) (parabolicLeviProjection G I) l
  exact (congrArg (leviPointsMulEquiv G I) hc).trans
    (hproj.trans (hgroup.trans (congrArg (leviPointsMulEquiv G I)
      (Variety.mapPoints_id l).symm)))

/-- The rational kernel of the Levi projection is the outside-subsystem positive-root group. -/
theorem parabolicLeviProjection_kernel (I : Set G.rootBase.support)
    (p : (standardParabolicVariety G I).points) :
    Variety.mapPoints (parabolicLeviProjection G I) p = 1 ↔
      (parabolicPointsMulEquiv G I p : G.points) ∈ parabolicUnipotentPoints G I := by
  have hproj := parabolicLeviProjection_points G I p
  constructor
  · intro hp
    have hz : parabolicPointProjection G I (parabolicPointsMulEquiv G I p) = 1 :=
      hproj.symm.trans ((congrArg (leviPointsMulEquiv G I) hp).trans (map_one _))
    change parabolicPointsMulEquiv G I p ∈ unipotentInParabolic G I
    rw [← parabolicPointProjection_ker]
    exact hz
  · intro hp
    have hz : parabolicPointProjection G I (parabolicPointsMulEquiv G I p) = 1 := by
      change parabolicPointsMulEquiv G I p ∈ (parabolicPointProjection G I).ker
      rw [parabolicPointProjection_ker]
      exact hp
    apply (leviPointsMulEquiv G I).injective
    exact hproj.trans (hz.trans (map_one (leviPointsMulEquiv G I)).symm)

/-- The regular Levi projection is surjective on schemes. -/
instance parabolicLeviProjection_surjective (I : Set G.rootBase.support) :
    Surjective (parabolicLeviProjection G I).left := by
  refine ⟨fun l => ⟨(leviParabolicInclusion G I).left l, ?_⟩⟩
  have hc := congrArg (fun f : (leviVariety G I).toOver ⟶ (leviVariety G I).toOver => f.left)
    (parabolicLeviProjection_section G I)
  exact congrArg (fun f : (leviVariety G I).scheme ⟶ (leviVariety G I).scheme => f l) hc

end SchubertGeometry
