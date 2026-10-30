import OrbitComplexity.SchubertGeometry.BSDH.Construction
import OrbitComplexity.SchubertGeometry.FlagBundle.Points
/-! # Represented points in BSDH append pullbacks

A lift of the preceding endpoint and a point of the next simple Schubert variety
give a rational point of the appended BSDH scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
private abbrev simpleFibre (i : G.rootBase.support) : GroupActions.Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
private abbrev simpleProjection (i : G.rootBase.support) :=
  flagBundleProjection G (simpleFibre G i)
private abbrev simpleEndpoint (i : G.rootBase.support) :=
  flagBundleMap G (simpleFibre G i)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

/-- The BSDH point obtained by appending a simple-Schubert point to a represented endpoint. -/
def bsdhAppendPoint (word : List G.rootBase.support) (i : G.rootBase.support)
    (z : Spec (CommRingCat.of K) ⟶ bsdhScheme G word) (g : G.points)
    (hz : z ≫ bsdhMap G word = (flagVarietyPointsEquiv G (flagProjection G g)).val)
    (y : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    Spec (CommRingCat.of K) ⟶ bsdhScheme G (word ++ [i]) :=
  pullback.lift z (flagBundlePoint G (simpleFibre G i) g y)
    (hz.trans (flagBundlePoint_projection G (simpleFibre G i) g y).symm) ≫
      (bsdhAppendIso G word i).inv.left

/-- Forgetting the appended BSDH factor recovers the preceding point. -/
theorem bsdhAppendPoint_fst (word : List G.rootBase.support) (i : G.rootBase.support)
    (z : Spec (CommRingCat.of K) ⟶ bsdhScheme G word) (g : G.points)
    (hz : z ≫ bsdhMap G word = (flagVarietyPointsEquiv G (flagProjection G g)).val)
    (y : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    bsdhAppendPoint G word i z g hz y ≫ bsdhAppendFst G word i = z := by
  let e := (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i)
  change (pullback.lift z (flagBundlePoint G (simpleFibre G i) g y) _ ≫ e.inv) ≫
    (e.hom ≫ pullback.fst (bsdhMap G word) (simpleProjection G i)) = z
  rw [Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]

/-- The appended BSDH endpoint is the group translate of its simple-Schubert point. -/
theorem bsdhAppendPoint_endpoint (word : List G.rootBase.support) (i : G.rootBase.support)
    (z : Spec (CommRingCat.of K) ⟶ bsdhScheme G word) (g : G.points)
    (hz : z ≫ bsdhMap G word = (flagVarietyPointsEquiv G (flagProjection G g)).val)
    (y : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    bsdhAppendPoint G word i z g hz y ≫ bsdhMap G (word ++ [i]) =
      (GroupActions.reductivePointsMulEquiv G g • GroupActions.Variety.mapPoints
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) y).val := by
  have he : (bsdhAppendIso G word i).inv.left ≫ bsdhMap G (word ++ [i]) =
      pullback.snd (bsdhMap G word) (simpleProjection G i) ≫ simpleEndpoint G i :=
    (bsdhAppendIso G word i).inv.w
  dsimp only [bsdhAppendPoint]
  rw [Category.assoc, he, pullback.lift_snd_assoc]
  exact flagBundlePoint_map G (simpleFibre G i)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) g y

end SchubertGeometry
