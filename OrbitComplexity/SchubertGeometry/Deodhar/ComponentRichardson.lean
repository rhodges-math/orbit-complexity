import OrbitComplexity.SchubertGeometry.Deodhar.Components
import OrbitComplexity.SchubertGeometry.Cells.ClosureStability

/-! # Intrinsic components inside Richardson strata

The final opposite-cell condition and the ambient ordinary cell place an intrinsic component
inside its open Richardson stratum. The reduced induced structures give a regular immersion.
-/

open CategoryTheory AlgebraicGeometry Topology ReductiveGroups SchubertGeometry GroupActions
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : BruhatIntervals.Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem cell_range_cast {a b : G.weylGroup} (h : a = b) :
    Set.range (Variety.mapPoints (schubertCellInclusion G a)) =
      Set.range (Variety.mapPoints (schubertCellInclusion G b)) := by
  subst b
  rfl

private theorem richardson_points (x : (deodharComponent G expression hred).points) :
    Variety.mapPoints (deodharInclusion G expression hred) x ∈
      Set.range (Variety.mapPoints (richardsonCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word))) := by
  let y := Variety.mapPoints (deodharPrefixInclusion G expression hred word.length) x
  have hc := Variety.mapPoints_comp (X := deodharComponent G expression hred)
    (Y := wordCell G word word.length) (Z := flagVariety G)
    (deodharPrefixInclusion G expression hred word.length)
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))) x
  have hord : Variety.mapPoints (deodharInclusion G expression hred) x ∈
      Set.range (Variety.mapPoints (schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take word.length)))) := ⟨y, hc.symm⟩
  have hx := (mem_deodharPrefix_points G expression hred word.length y).mp ⟨x, rfl⟩
  have hop := hx (Fin.last word.length)
  rw [wordCellProjection_self G word hred word.length, Category.id_comp] at hop
  change Variety.mapPoints
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))) y ∈ _ at hop
  rw [← hc] at hop
  rw [richardsonCell_points_range]
  exact ⟨(cell_range_cast G (congrArg (simpleWeylWord G.rootBase)
    (show word.take word.length = word from List.take_length))).subset hord, hop⟩

private theorem richardson_range :
    Set.range (deodharInclusion G expression hred).left ⊆
      Set.range (richardsonCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word)).left := by
  apply Variety.range_subset_of_mapPoints
  rintro _ ⟨x, rfl⟩
  exact richardson_points G expression hred x

/-- An intrinsic component maps regularly into the Richardson stratum of its final product. -/
def deodharRichardsonMap :
    (deodharComponent G expression hred).toOver ⟶
      (richardsonCell G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word)).toOver := by
  let f := deodharInclusion G expression hred
  let i := richardsonCellInclusion G
    (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
    (simpleWeylWord G.rootBase word)
  let f₀ : (deodharComponent G expression hred).scheme ⟶ (flagVariety G).scheme := f.left
  let i₀ : (richardsonCell G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
      (simpleWeylWord G.rootBase word)).scheme ⟶ (flagVariety G).scheme := i.left
  let g := GroupActions.liftPreimmersion i₀ f₀ (richardson_range G expression hred)
  have hg : g ≫ i₀ = f₀ := GroupActions.liftPreimmersion_fac i₀ f₀ _
  exact Over.homMk g (by
    rw [← i.w, ← Category.assoc, hg]
    exact f.w)

/-- The component map into its Richardson stratum preserves its flag inclusion. -/
@[reassoc]
theorem deodharRichardsonMap_comp :
    deodharRichardsonMap G expression hred ≫ richardsonCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
      (simpleWeylWord G.rootBase word) = deodharInclusion G expression hred := by
  apply Over.OverMorphism.ext
  let f₀ : (deodharComponent G expression hred).scheme ⟶ (flagVariety G).scheme :=
    (deodharInclusion G expression hred).left
  let i₀ : (richardsonCell G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
      (simpleWeylWord G.rootBase word)).scheme ⟶ (flagVariety G).scheme :=
    (richardsonCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
      (simpleWeylWord G.rootBase word)).left
  exact GroupActions.liftPreimmersion_fac i₀ f₀ (richardson_range G expression hred)

attribute [local irreducible] deodharRichardsonMap

omit [IsAlgClosed K] [CharZero K] in
private instance locallyClosedImmersion (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) : IsImmersion (X.locallyClosedInclusion S hS).left where
  isLocallyClosed_range := by rw [Variety.locallyClosedInclusion_range]; exact hS

private instance cellImmersion (w : G.weylGroup) :
    IsImmersion (schubertCellInclusion G w).left where
  isLocallyClosed_range := by
    rw [GroupActions.orbitInclusion_range]
    exact orbitImage_locallyClosed _ _ _

private theorem flagImmersion : IsImmersion (deodharInclusion G expression hred).left :=
  inferInstanceAs (IsImmersion
    ((deodharPrefixInclusion G expression hred word.length).left ≫
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))).left))

/-- The intrinsic component map into its Richardson stratum is a locally closed immersion. -/
instance deodharRichardsonMap_isImmersion :
    IsImmersion (deodharRichardsonMap G expression hred).left := by
  let i := richardsonCellInclusion G
    (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
    (simpleWeylWord G.rootBase word)
  have hc : (deodharRichardsonMap G expression hred).left ≫ i.left =
      (deodharInclusion G expression hred).left :=
    congrArg (fun f : (deodharComponent G expression hred).toOver ⟶
      (flagVariety G).toOver => f.left) (deodharRichardsonMap_comp G expression hred)
  have : IsImmersion ((deodharRichardsonMap G expression hred).left ≫ i.left) := by
    rw [hc]
    exact flagImmersion G expression hred
  exact IsImmersion.of_comp _ i.left


end
end SchubertGeometry
