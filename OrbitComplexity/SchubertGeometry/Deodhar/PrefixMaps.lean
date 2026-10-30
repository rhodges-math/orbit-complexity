import OrbitComplexity.SchubertGeometry.Deodhar.ChartTransport
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.GroupActions.Actions.Points
/-! # Maps on increasing prefix cells

A regular group lift over a prefix cell gives the additive extension map in the next cell.
Its projection and point action follow from the relative rank-one chart.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups SchubertGeometry
open GroupActions GroupActions.Variety
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
private theorem pair_action {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X Y H D : C} [MonObj H] [ModObj H D]
    (m : X ⊗ Y ⟶ D) (g : X ⟶ H) (v : Y ⟶ D)
    (hm : ∀ (Z : C) (x : Z ⟶ X) (y : Z ⟶ Y),
      lift x y ≫ m = (x ≫ g) • (y ≫ v)) {Z : C} (a : Z ⟶ X ⊗ Y) :
    a ≫ m = (a ≫ fst X Y ≫ g) • (a ≫ snd X Y ≫ v) := by
  have h := hm Z (a ≫ fst X Y) (a ≫ snd X Y)
  rw [lift_comp_fst_snd] at h
  simpa only [Category.assoc] using h

private theorem point_comp {K : Type u} [Field K] {X Y : Variety K}
    (f : X.toOver ⟶ Y.toOver) (x : X.points) :
    Y.pointsEquivOverHom (mapPoints f x) = X.pointsEquivOverHom x ≫ f := rfl

private theorem pair_action_points {K : Type u} [Field K] {X Y H D Q : Variety K}
    [GrpObj H.toOver] [ModObj H.toOver D.toOver]
    (m : X.toOver ⊗ Y.toOver ⟶ D.toOver) (g : X.toOver ⟶ H.toOver)
    (v : Y.toOver ⟶ D.toOver)
    (hm : ∀ (Z : Over (Spec (CommRingCat.of K))) (x : Z ⟶ X.toOver) (y : Z ⟶ Y.toOver),
      lift x y ≫ m = (x ≫ g) • (y ≫ v))
    (a : Q.toOver ⟶ X.toOver ⊗ Y.toOver) (q : Q.points) :
    mapPoints (a ≫ m) q =
      mapPoints (a ≫ fst X.toOver Y.toOver ≫ g) q •
        mapPoints (a ≫ snd X.toOver Y.toOver ≫ v) q := by
  apply D.pointsEquivOverHom.injective
  rw [point_comp, pointsEquivOverHom_smul, point_comp, point_comp]
  simpa only [Category.assoc] using pair_action m g v hm (Q.pointsEquivOverHom q ≫ a)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (n : ℕ) (hn : n < word.length)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
    (simpleWeylWord G.rootBase (word.take n)) word[n]))
  (X : Variety K)
  (f : X.toOver ⟶ (schubertCell G (simpleWeylWord G.rootBase (word.take n))).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫
    schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)))

/-- The additive prefix extension projects to the prescribed preceding-cell morphism. -/
theorem wordLiftMap_projection :
    ((rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi) ≫
        (wordCellExtensionIso G word n hn).hom) ≫ wordCellStep G word hred n =
      fst X.toOver (additiveVariety K).toOver ≫ f :=
  rankOneLiftMap_projection G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X
    (wordCell G word (n + 1)) f g hg (wordCellExtensionIso G word n hn).hom
    (wordCellStep G word hred n) (wordCellExtensionIso_projection G word hred n hn hi)

private theorem wordLiftMap_action (Z : Over (Spec (CommRingCat.of K))) (x : Z ⟶ X.toOver)
    (y : Z ⟶ (additiveVariety K).toOver) :
    lift x y ≫ ((rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n]
      hi X f g hg).hom ≫ pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi) ≫
          (wordCellExtensionIso G word n hn).hom ≫
            schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) =
      (x ≫ g) • (y ≫ (simpleCellIso G word[n]).hom ≫
        schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem word[n])) :=
  lift_rankOneLiftMap_action G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X
    (wordCell G word (n + 1)) f g hg (wordCellExtensionIso G word n hn).hom
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1))))
    (wordCellExtensionIso_flag G word n hn) Z x y

/-- Rational points of a prefix extension use its regular group frame and simple-cell coordinate. -/
theorem wordLiftMap_points (Q : Variety K)
    (a : Q.toOver ⟶ X.toOver ⊗ (additiveVariety K).toOver) (q : Q.points) :
    mapPoints (a ≫
      (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi) ≫
      (wordCellExtensionIso G word n hn).hom ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) q =
      mapPoints (a ≫ fst X.toOver (additiveVariety K).toOver ≫ g) q •
        mapPoints (a ≫ snd X.toOver (additiveVariety K).toOver ≫
          (simpleCellIso G word[n]).hom ≫
          schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem word[n])) q := by
  exact pair_action_points
    ((rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi) ≫
      (wordCellExtensionIso G word n hn).hom ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) g
    ((simpleCellIso G word[n]).hom ≫
      schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem word[n]))
    (wordLiftMap_action G word n hn hi X f g hg) a q

end
end SchubertGeometry
