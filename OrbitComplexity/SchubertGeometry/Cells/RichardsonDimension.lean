import OrbitComplexity.SchubertGeometry.Deodhar.ComponentIsomorphisms
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterDimensions
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentCover
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentRichardson
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIntegral
import OrbitComplexity.SchubertGeometry.Parabolics.Order
import OrbitComplexity.BruhatIntervals.Words.Positive
import OrbitComplexity.GroupActions.Varieties.ImageCovers

/-! # Richardson dimensions

A finite component cover bounds the dimension from above. The positive distinguished
component gives the matching lower bound, and the open stratum is dense in its closure.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open GroupActions GroupActions.Variety ReductiveGroups BruhatIntervals SchubertGeometry
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
attribute [local irreducible] deodharParameters deodharComponentIso

private theorem component_irreducible (expression : Subexpression word)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    IrreducibleSpace (deodharComponent G expression hred).scheme := by
  let e : (deodharParameters G expression).toOver ≅
      (deodharComponent G expression hred).toOver :=
    deodharComponentIso G expression hred hd
  let e₀ : (deodharParameters G expression).scheme ≅
      (deodharComponent G expression hred).scheme := (Over.forget _).mapIso e
  exact e₀.hom.homeomorph.irreducibleSpace_iff.mp
    (deodharParameters_irreducible G expression)

private theorem component_dim_le (expression : Subexpression word)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    (deodharComponent G expression hred).dim ≤
      ((word.length - (weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) : ℕ) :
          WithBot ℕ∞) := by
  let e : (deodharParameters G expression).toOver ≅
      (deodharComponent G expression hred).toOver :=
    deodharComponentIso G expression hred hd
  exact (Variety.dim_eq_of_iso (deodharParameters G expression) e).symm.le.trans
    (deodharParameters_dim_le G expression)

private theorem positive_component_dim (expression : Subexpression word)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hp : IsPositive (weylCoxeterSystem G.rootBase) expression) :
    (deodharComponent G expression hred).dim =
      ((word.length - (weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) : ℕ) :
          WithBot ℕ∞) := by
  let e : (deodharParameters G expression).toOver ≅
      (deodharComponent G expression hred).toOver :=
    deodharComponentIso G expression hred hd
  exact (Variety.dim_eq_of_iso (deodharParameters G expression) e).symm.trans
    (positiveParameters_dim G expression hp)

private instance richardson_immersion (a b : G.weylGroup) :
    IsImmersion (richardsonCellInclusion G a b).left where
  isLocallyClosed_range := by
    rw [richardsonCellInclusion_range, GroupActions.orbitInclusion_range,
      GroupActions.orbitInclusion_range]
    exact (orbitImage_locallyClosed _ _ _).inter (orbitImage_locallyClosed _ _ _)

private instance component_immersion (e : Subexpression word)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    IsImmersion (deodharInclusion G e hred).left := by
  let f := deodharRichardsonMap G e hred
  let j := richardsonCellInclusion G
    (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
    (simpleWeylWord G.rootBase word)
  have hf : IsImmersion (f.left ≫ j.left) := inferInstance
  have hc : f.left ≫ j.left = (deodharInclusion G e hred).left :=
    congrArg (fun m : (deodharComponent G e hred).toOver ⟶
      (flagVariety G).toOver => m.left) (deodharRichardsonMap_comp G e hred)
  rwa [hc] at hf

private theorem richardson_dim_word
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (a : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a
      ((weylCoxeterSystem G.rootBase).wordProd word)) :
    (richardsonCell G a (simpleWeylWord G.rootBase word)).dim =
      ((word.length - (weylCoxeterSystem G.rootBase).length a : ℕ) : WithBot ℕ∞) := by
  classical
  apply le_antisymm
  · let ι := {e : Subexpression word //
      IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
        e.prefixProd (weylCoxeterSystem G.rootBase) word.length = a}
    let : ∀ e : ι, IrreducibleSpace (deodharComponent G e.val hred).scheme :=
      fun e => component_irreducible G e.val hred e.property.1
    apply Variety.dim_le_of_finite_image_cover
      (richardsonCellInclusion G a (simpleWeylWord G.rootBase word))
      (fun e : ι => deodharComponent G e.val hred)
      (fun e : ι => deodharInclusion G e.val hred)
      (deodharRichardson_cover G word hred a).symm
    intro e
    have h := component_dim_le G e.val hred e.property.1
    rwa [e.property.2] at h
  · obtain ⟨e, he, _⟩ := positive_subexpression_unique
      (weylCoxeterSystem G.rootBase) hred a hle
    have hdim := positive_component_dim G e hred he.2.1 he.2.2
    have him := (deodharRichardsonMap G e hred).left.isEmbedding.isInducing.topologicalKrullDim_le
    change (deodharComponent G e hred).dim ≤
      (richardsonCell G (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word)).dim at him
    rw [he.1] at him hdim
    exact hdim.symm.le.trans him

/-- The dimension of a Richardson variety is the difference of its endpoint lengths. -/
theorem richardsonVariety_dim (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    (richardsonVariety G a b).dim =
      (((weylCoxeterSystem G.rootBase).length b -
        (weylCoxeterSystem G.rootBase).length a : ℕ) : WithBot ℕ∞) := by
  obtain ⟨word, hred, hprod⟩ := (weylCoxeterSystem G.rootBase).exists_isReduced b
  have hb : simpleWeylWord G.rootBase word = b := by
    simpa only [weylCoxeterSystem_wordProd] using hprod.symm
  have hl : (weylCoxeterSystem G.rootBase).BruhatLE a
      ((weylCoxeterSystem G.rootBase).wordProd word) := by
    rwa [← hprod]
  have hword := richardson_dim_word G hred a hl
  rw [hb] at hword
  have he := richardsonCell_dim_eq G a b ((weyl_bruhat_iff G.rootBase a b).mpr hle)
  rw [he] at hword
  have hlen : word.length = (weylCoxeterSystem G.rootBase).length b := by
    simpa only [hprod] using hred.eq.symm
  rwa [hlen] at hword

/-- The natural dimension of a Richardson variety is its endpoint length difference. -/
theorem richardsonVariety_natDim (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    (richardsonVariety G a b).natDim =
      (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a := by
  unfold Variety.natDim
  rw [richardsonVariety_dim G a b hle]
  exact ENat.toNat_natCast _

end
end SchubertGeometry
