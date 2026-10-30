import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Batteries.Tactic.Lint

/-! # Cartesian nodes through three coefficient extensions

The Cartesian squares for three coefficient changes and the Cartesian square
for the prescribed total space determine the square of each original node.
The proof uses only projection equations and the original node isomorphism.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry.RetainedCharacter

universe u v

/-- Three successive Cartesian coefficient changes identify a node with the
inverse image of its original colimit chart in the prescribed total space. -/
theorem scalarNode_isPullback {C : Type u} [Category.{v} C]
    {S₀ S T K P₀ PS PT PK D X₀ X : C}
    (cS : PS ⟶ P₀) (cT : PT ⟶ PS) (cK : PK ⟶ PT)
    (p₀ : P₀ ⟶ S₀) (pS : PS ⟶ S) (pT : PT ⟶ T) (pK : PK ⟶ K)
    (βS : S ⟶ S₀) (βT : T ⟶ S) (βK : K ⟶ T)
    (hS : IsPullback cS pS p₀ βS) (hT : IsPullback cT pT pS βT)
    (hK : IsPullback cK pK pT βK)
    (E : D ≅ P₀) (leg : D ⟶ X₀) (base₀ : X₀ ⟶ S₀)
    (q : X ⟶ X₀) (base : X ⟶ K)
    (hq : IsPullback q base base₀ (βK ≫ βT ≫ βS))
    (node : PK ⟶ X)
    (hOld : (E.inv ≫ leg) ≫ base₀ = p₀)
    (hnode : node ≫ q = (cK ≫ cT ≫ cS) ≫ E.inv ≫ leg)
    (hbase : node ≫ base = pK) :
    IsPullback ((cK ≫ cT ≫ cS) ≫ E.inv) node leg q := by
  let c : PK ⟶ P₀ := cK ≫ cT ≫ cS
  have hc : IsPullback c pK p₀ (βK ≫ βT ≫ βS) := by
    simpa only [Category.assoc] using (hK.paste_horiz hT).paste_horiz hS
  have houter : IsPullback c (node ≫ base) ((E.inv ≫ leg) ≫ base₀)
      (βK ≫ βT ≫ βS) := by
    rw [hbase, hOld]
    exact hc
  have hn : IsPullback c node (E.inv ≫ leg) q :=
    houter.of_bot hnode.symm hq
  have hi : IsPullback E.inv (E.inv ≫ leg) leg (𝟙 X₀) :=
    IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
  simpa only [Category.comp_id] using hn.paste_horiz hi

end SchubertGeometry.RetainedCharacter
