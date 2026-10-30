import OrbitComplexity.SchubertGeometry.BSDH.OpenCell
import OrbitComplexity.FrobeniusSplitting.Normality.ProperPushforward
import OrbitComplexity.SchubertGeometry.FlagVariety.Properties
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth

/-! # Birationality of the longest BSDH endpoint -/

noncomputable section
namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory ReductiveGroups TopologicalSpace

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- A reduced longest word gives a birational morphism to the flag variety. -/
theorem bsdh_longest_birational (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : simpleWeylWord G.rootBase word = G.longestElement) :
    Scheme.BirationalOver (bsdhMap G word) (𝟙 (flagVariety G).scheme) := by
  obtain ⟨c, hopen, hc⟩ :
      ∃ c : (schubertCell G G.longestElement).scheme ⟶ bsdhScheme G word,
        IsOpenImmersion c ∧
          c ≫ bsdhMap G word = (schubertCellInclusion G G.longestElement).left := by
    exact Eq.mp (congrArg (fun w : G.weylGroup ↦
      ∃ c : (schubertCell G w).scheme ⟶ bsdhScheme G word,
        IsOpenImmersion c ∧
          c ≫ bsdhMap G word = (schubertCellInclusion G w).left) hw)
      (bsdh_cell_open G word hred)
  let : IsOpenImmersion c := hopen
  have : IsDominant c := ⟨c.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty c)⟩
  have : IsIso (schubertInclusion G G.longestElement).left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).mapIso
      (longestSchubertIso G)).hom)
  have : IsOpenImmersion (schubertCellInclusion G G.longestElement).left := by
    rw [← congrArg Over.Hom.left (schubertCellOfLE_comp G G.longestElement
      G.longestElement (WeylBruhatLE.refl G.rootBase G.longestElement))]
    change IsOpenImmersion (_ ≫ _)
    infer_instance
  have : IsDominant (schubertCellInclusion G G.longestElement).left :=
    ⟨longestCell_dense G⟩
  exact (c.birationalOver (bsdhMap G word)
    (schubertCellInclusion G G.longestElement).left hc).symm.trans
      ((schubertCellInclusion G G.longestElement).left.birationalOver
        (𝟙 (flagVariety G).scheme) (schubertCellInclusion G G.longestElement).left
        (Category.comp_id _))

/-- The longest BSDH endpoint preserves the structure sheaf of the flag variety. -/
theorem bsdh_longest_pushforward (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : simpleWeylWord G.rootBase word = G.longestElement) :
    IsIso (bsdhMap G word).c :=
  FrobeniusSplitting.proper_birational_sheaf (bsdhMap G word)
    (bsdh_longest_birational G word hred hw)
    fun y ↦ (FrobeniusSplitting.stalks_of_smooth (flagVariety G).toSpec y).2

end SchubertGeometry
