import OrbitComplexity.SchubertGeometry.Deodhar.RelativeChart
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.SchubertGeometry.Deodhar.ProductAction
/-! # Multiplication in relative cell charts

The Borel comparison factor changes the additive coordinate so that the resulting relative
chart multiplies the prescribed regular group lift by the chosen simple-cell flag.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2, diagram (5.3).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem borel_hom_smul (Z : Over (Spec (CommRingCat.of K)))
    (b : Z ⟶ (GroupActions.borelVariety G).toOver) (x : Z ⟶ (flagVariety G).toOver) :
    b • x = (b ≫ GroupActions.borelInclusion G) • x := by
  change lift b x ≫ ((GroupActions.borelInclusion G ▷ (flagVariety G).toOver) ≫
      ModObj.smul (M := (GroupActions.reductiveVariety G).toOver)
        (X := (flagVariety G).toOver)) =
    lift (b ≫ GroupActions.borelInclusion G) x ≫
      ModObj.smul (M := (GroupActions.reductiveVariety G).toOver)
        (X := (flagVariety G).toOver)
  rw [← Category.assoc, lift_whiskerRight]

private theorem post_chart {C : Type*} [Category C] {A B E F Q Z : C}
    (e : A ⟶ Q) (p : Q ⟶ E) (j : E ⟶ F) (t : A ⟶ A) (v : A ⟶ B) (c : B ⟶ E)
    (h : e ≫ p = t ≫ (v ≫ c)) (q : Z ⟶ A) :
    q ≫ (e ≫ p ≫ j) = q ≫ (t ≫ (v ≫ (c ≫ j))) := by
  rw [← Category.assoc e p j, h]
  simp only [Category.assoc]

private theorem twisted_action {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X A D H B S F Z : C} [MonObj H] [MonObj B]
    [ModObj H F] [ModObj B S] [ModObj B F]
    (f : X ⟶ D) (l : D ⟶ H) (b : X ⟶ B) (g : X ⟶ H) (incl : B ⟶ H)
    (s : A ≅ S) (j : S ⟶ F) [IsModHom B j]
    (t : X ⊗ A ⟶ X ⊗ A) (c : D ⊗ A ⟶ F)
    (hc : c = (fst D A ≫ l) • (snd D A ≫ s.hom ≫ j))
    (hframe : (f ≫ l) * (b ≫ incl) = g)
    (hrestrict : ∀ {V : C} (a : V ⟶ B) (z : V ⟶ F), a • z = (a ≫ incl) • z)
    (x : Z ⟶ X) (y : Z ⟶ A)
    (ht : lift x y ≫ t = lift x (((x ≫ b) • (y ≫ s.hom)) ≫ s.inv)) :
    lift x y ≫ (t ≫ ((f ⊗ₘ 𝟙 A) ≫ c)) = (x ≫ g) • (y ≫ s.hom ≫ j) := by
  rw [← Category.assoc, ht, ← Category.assoc, lift_map, Category.comp_id,
    hc, ModObj.comp_smul, lift_fst_assoc, lift_snd_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [IsModHom.map_smul, hrestrict, ← mul_smul,
    Category.assoc x b incl, ← MonObj.comp_mul, hframe]
  simp only [Category.assoc]

variable (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
  (X : GroupActions.Variety K)
  (f : X.toOver ⟶ (schubertCell G w).toOver)
  (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w)

/-- The relative chart extends the given regular group lift by its simple-cell coordinate. -/
theorem lift_rankOneLiftIso_action (Z : Over (Spec (CommRingCat.of K)))
    (x : Z ⟶ X.toOver) (y : Z ⟶ (GroupActions.additiveVariety K).toOver) :
    lift x y ≫ ((rankOneLiftIso G w i hw X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G w i hw) ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) =
      (x ≫ g) • (y ≫ (simpleCellIso G i).hom ≫
        schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i)) := by
  have hrel := post_chart (rankOneLiftIso G w i hw X f g hg).hom
    (pullback.snd f (rankOneCellProjection G w i hw))
    (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i))
    (rankOneLiftTwist G w i X f g hg).hom (f ⊗ₘ 𝟙 (GroupActions.additiveVariety K).toOver)
    (rankOneCellProductIso G w i hw).hom (rankOneLiftIso_snd G w i hw X f g hg) (lift x y)
  exact hrel.trans (twisted_action f (schubertCellLift G w)
    (schubertBorelLift G w X f g hg) g (GroupActions.borelInclusion G)
    (simpleCellIso G i)
    (schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))
    (rankOneLiftTwist G w i X f g hg).hom
    ((rankOneCellProductIso G w i hw).hom ≫ schubertCellInclusion G
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i))
    (rankOneCellProductIso_action G w i hw)
    (schubertBorelLift_mul G w X f g hg) (fun _ _ => borel_hom_smul G _ _ _)
    x y (lift_rankOneLiftTwist G w i X f g hg Z x y))

end
end SchubertGeometry
