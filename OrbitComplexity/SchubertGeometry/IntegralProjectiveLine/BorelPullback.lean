import OrbitComplexity.SchubertGeometry.ProjectiveLine.BorelAction
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelFamilies

/-! # Borel actions through singleton Levi coordinates -/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem tensor_iso_cancel {C : Type*} [Category C] [MonoidalCategory C]
    {A B D X P : C} (f : A ⟶ B) (e : D ≅ B) (g : P ⟶ X) :
    ((f ≫ e.inv) ⊗ₘ 𝟙 P) ≫ (e.hom ⊗ₘ g) = f ⊗ₘ g := by
  rw [tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private theorem tensor_restriction {C : Type*} [Category C] [MonoidalCategory C]
    {A B X P : C} (f : A ⟶ B) (g : P ⟶ X) :
    (𝟙 A ⊗ₘ g) ≫ (f ▷ X) = f ⊗ₘ g := by
  rw [tensorHom_comp_whiskerRight]
  simp only [Category.id_comp]

private theorem restricted_family {C : Type*} [Category C] [MonoidalCategory C]
    {A B D L X P : C} (f : A ⟶ B) (e : D ≅ B) (t : X ≅ P) (j : B ⟶ L)
    (mB : B ⊗ X ⟶ X) (mL : L ⊗ X ⟶ X) (F : D ⊗ P ⟶ P)
    (hm : mB = (j ▷ X) ≫ mL)
    (hF : (e.hom ⊗ₘ t.inv) ≫ (j ▷ X) ≫ mL ≫ t.hom = F) :
    (𝟙 A ⊗ₘ t.inv) ≫ ((f ▷ X) ≫ mB) ≫ t.hom = ((f ≫ e.inv) ⊗ₘ 𝟙 P) ≫ F := by
  have h := congrArg (fun m => ((f ≫ e.inv) ⊗ₘ 𝟙 P) ≫ m) hF
  have hc := tensor_iso_cancel f e t.inv
  have ht := tensor_restriction f t.inv
  rw [hm]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ht]
  simpa only [← Category.assoc, hc] using h

private theorem leviBorel_action (i : G.rootBase.support) :
    ModObj.smul (M := (leviBorelVariety G {i}).toOver)
        (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) =
      (leviBorelLeviInclusion G {i} ▷
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
      ModObj.smul (M := (leviVariety G {i}).toOver)
        (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) := by
  have hFlag : (leviBorelLeviInclusion G {i} ▷ (flagVariety G).toOver) ≫
      ModObj.smul (M := (leviVariety G {i}).toOver) (X := (flagVariety G).toOver) =
        ModObj.smul (M := (leviBorelVariety G {i}).toOver) (X := (flagVariety G).toOver) := by
    change (leviBorelLeviInclusion G {i} ▷ (flagVariety G).toOver) ≫
      ((leviInclusion G {i} ▷ (flagVariety G).toOver) ≫
        ModObj.smul (M := (reductiveVariety G).toOver) (X := (flagVariety G).toOver)) =
      (leviBorelInclusion G {i} ▷ (flagVariety G).toOver) ≫
        ModObj.smul (M := (reductiveVariety G).toOver) (X := (flagVariety G).toOver)
    rw [← comp_whiskerRight_assoc, leviBorelLeviInclusion_comp]
  have : Mono (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :=
    Over.mono_of_mono_left _
  apply (cancel_mono
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))).mp
  rw [IsModHom.smul_hom, Category.assoc, IsModHom.smul_hom]
  change ((leviBorelVariety G {i}).toOver ◁
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ≫
    ModObj.smul (M := (leviBorelVariety G {i}).toOver) (X := (flagVariety G).toOver) =
    (leviBorelLeviInclusion G {i} ▷
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
    ((leviVariety G {i}).toOver ◁
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ≫
    ModObj.smul (M := (leviVariety G {i}).toOver) (X := (flagVariety G).toOver)
  rw [← Category.assoc, ← whisker_exchange, Category.assoc, hFlag]

/-- The full Borel action is the affine projective family pulled back through its Levi quotient. -/
theorem simpleBorel_affine_family (i : G.rootBase.support) :
    letI := simpleBorelAction G i
    ((𝟙 (borelVariety G).toOver ⊗ₘ (simpleSchubertIso G i).inv) ≫
      ModObj.smul (M := (borelVariety G).toOver)
        (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
      (simpleSchubertIso G i).hom) =
    (((simpleBorelProjection G i ≫ (simpleBorelTensorIso G i).inv) ⊗ₘ
        𝟙 (projectiveVariety K (ULift.{u} (Fin 2))).toOver) ≫
      projectiveAffineFamily (algebraMap K (simpleBorelCoefficientAlgebra G))
        (simpleRootCoefficient G i)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
          simpleRootParameter G)) := by
  let := simpleBorelAction G i
  change (𝟙 (borelVariety G).toOver ⊗ₘ (simpleSchubertIso G i).inv) ≫
    ((simpleBorelProjection G i ▷
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
      ModObj.smul (M := (leviBorelVariety G {i}).toOver)
        (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver)) ≫
    (simpleSchubertIso G i).hom = _
  exact restricted_family (simpleBorelProjection G i) (simpleBorelTensorIso G i)
    (simpleSchubertIso G i) (leviBorelLeviInclusion G {i})
    (ModObj.smul (M := (leviBorelVariety G {i}).toOver)
      (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver))
    (ModObj.smul (M := (leviVariety G {i}).toOver)
      (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver))
    _ (leviBorel_action G i) (simpleLeviBorel_affine_family G i)

end SchubertGeometry
end
