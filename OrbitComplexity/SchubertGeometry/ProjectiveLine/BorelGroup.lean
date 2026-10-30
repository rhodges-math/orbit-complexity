import OrbitComplexity.SchubertGeometry.ProjectiveLine.BorelProjection

/-! # Group compatibility of the singleton Borel projection -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions MonoidalCategory
open scoped CategoryTheory.MonObj
universe u v

private theorem monHom_cancel {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {M N P : C} [MonObj M] [MonObj N] [MonObj P]
    (f : M ⟶ N) (i : N ⟶ P) [Mono i] [IsMonHom i] [IsMonHom (f ≫ i)] :
    IsMonHom f := by
  constructor
  · apply (cancel_mono i).mp
    calc
      (η[M] ≫ f) ≫ i = η[M] ≫ (f ≫ i) := Category.assoc _ _ _
      _ = η[P] := IsMonHom.one_hom (f ≫ i)
      _ = η[N] ≫ i := (IsMonHom.one_hom i).symm
  · apply (cancel_mono i).mp
    calc
      (μ[M] ≫ f) ≫ i = μ[M] ≫ (f ≫ i) := Category.assoc _ _ _
      _ = ((f ≫ i) ⊗ₘ (f ≫ i)) ≫ μ[P] := IsMonHom.mul_hom (f ≫ i)
      _ = ((f ⊗ₘ f) ≫ (i ⊗ₘ i)) ≫ μ[P] := by rw [tensorHom_comp_tensorHom]
      _ = (f ⊗ₘ f) ≫ ((i ⊗ₘ i) ≫ μ[P]) := Category.assoc _ _ _
      _ = (f ⊗ₘ f) ≫ (μ[N] ≫ i) :=
        congrArg (fun q => (f ⊗ₘ f) ≫ q) (IsMonHom.mul_hom i).symm
      _ = ((f ⊗ₘ f) ≫ μ[N]) ≫ i := (Category.assoc _ _ _).symm

private theorem monHom_cancel_eq {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {M N P : C} [MonObj M] [MonObj N] [MonObj P]
    (f : M ⟶ N) (i : N ⟶ P) (m : M ⟶ P) [Mono i] [IsMonHom i] [IsMonHom m]
    (h : f ≫ i = m) : IsMonHom f := by
  have : IsMonHom (f ≫ i) := h.symm ▸ inferInstanceAs (IsMonHom m)
  exact monHom_cancel f i

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private instance inclusion_mono (i : G.rootBase.support) :
    Mono (leviBorelLeviInclusion G {i}) := Over.mono_of_mono_left _

/-- The singleton Borel projection preserves the algebraic group operation. -/
instance simpleBorelProjection_isMonHom (i : G.rootBase.support) :
    type_of% (monHom_cancel_eq (simpleBorelProjection G i) (leviBorelLeviInclusion G {i})
      (borelParabolicInclusion G {i} ≫ parabolicLeviProjection G {i})
      (simpleBorelProjection_comp G i)) :=
  monHom_cancel_eq (simpleBorelProjection G i) (leviBorelLeviInclusion G {i})
    (borelParabolicInclusion G {i} ≫ parabolicLeviProjection G {i})
    (simpleBorelProjection_comp G i)

/-- On Borel points the singleton projection is the parabolic point-group projection. -/
theorem simpleBorelProjection_points (i : G.rootBase.support)
    (b : (borelVariety G).points) :
    (leviBorelPointsMulEquiv G {i} (Variety.mapPoints (simpleBorelProjection G i) b) :
      G.points) =
    (parabolicPointProjection G {i}
      (parabolicPointsMulEquiv G {i}
        (Variety.mapPoints (borelParabolicInclusion G {i}) b)) : G.points) := by
  have h := congrArg (fun f => Variety.mapPoints f b) (simpleBorelProjection_comp G i)
  rw [Variety.mapPoints_comp, Variety.mapPoints_comp] at h
  calc
    _ = (leviPointsMulEquiv G {i} (Variety.mapPoints (leviBorelLeviInclusion G {i})
        (Variety.mapPoints (simpleBorelProjection G i) b)) : G.points) :=
      (leviBorelLeviInclusion_points G {i} _).symm
    _ = (leviPointsMulEquiv G {i} (Variety.mapPoints (parabolicLeviProjection G {i})
        (Variety.mapPoints (borelParabolicInclusion G {i}) b)) : G.points) :=
      congrArg (fun x => (leviPointsMulEquiv G {i} x : G.points)) h
    _ = _ := congrArg Subtype.val (parabolicLeviProjection_points G {i} _)

end SchubertGeometry
