import OrbitComplexity.SchubertGeometry.Deodhar.StandardFormVariety
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentCover
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentDisjoint

/-! # The Deodhar decomposition by standard-form quotient images

The quotient images of the locally closed standard-form varieties cover the Richardson
stratum disjointly. Every scheme point lies in one unique distinguished quotient image.
-/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety
open scoped Pointwise
namespace SchubertGeometry
noncomputable section
universe u

private theorem preiso_range {K : Type u} [Field K] [IsAlgClosed K]
    {A B F : Variety K} (e : A.toOver ≅ B.toOver) (f : B.toOver ⟶ F.toOver) :
    Set.range (e.hom ≫ f).left = Set.range f.left := by
  apply Variety.range_eq_of_mapPoints
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨mapPoints e.hom a, (mapPoints_comp e.hom f a).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (pointsHomeomorph (X := A) (Y := B) e).surjective b
    exact ⟨a, mapPoints_comp e.hom f a⟩

private theorem transfer_partition {ι X : Type*} (S T : ι → Set X) (D : Set X)
    (heq : ∀ i, S i = T i) (hcover : (⋃ i, T i) = D)
    (hdis : ∀ a b x, x ∈ T a → x ∈ T b → a = b) :
    (⋃ i, S i) = D ∧ Pairwise (fun a b => Disjoint (S a) (S b)) := by
  constructor
  · exact (Set.iUnion_congr heq).trans hcover
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro x ha hb
    exact hab (hdis a b x ((heq a).subset ha) ((heq b).subset hb))

private theorem unique_of_partition {ι X : Type*} (S : ι → Set X) (D : Set X)
    (h : (⋃ i, S i) = D ∧ Pairwise (fun a b => Disjoint (S a) (S b)))
    (x : X) (hx : x ∈ D) : ∃! i, x ∈ S i := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h.1.symm ▸ hx)
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hn
  exact Set.disjoint_left.mp (h.2 hn) hj hi

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem standard_quotient_range (expression : Subexpression word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    Set.range (deodharStandardInclusion G expression hred hd ≫
      flagQuotientMorphism G).left = Set.range (deodharInclusion G expression hred).left := by
  have h := deodharStandardComponentIso_quotient G expression hred hd
  exact (congrArg (fun f : (deodharStandardVariety G expression hred hd).toOver ⟶
    (flagVariety G).toOver => Set.range f.left) h).symm.trans
      (preiso_range (deodharStandardComponentIso G expression hred hd)
        (deodharInclusion G expression hred))

/-- Standard-form quotient images give the disjoint scheme-point Richardson decomposition. -/
theorem deodharStandard_decomposition (v : G.weylGroup) :
    (⋃ e : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
        e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v},
      Set.range (deodharStandardInclusion G e.val hred e.property.1 ≫
        flagQuotientMorphism G).left) =
          Set.range (richardsonCellInclusion G v (simpleWeylWord G.rootBase word)).left ∧
    Pairwise (fun a b : {e : Subexpression word //
        IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
          e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v} =>
      Disjoint (Set.range (deodharStandardInclusion G a.val hred a.property.1 ≫
        flagQuotientMorphism G).left)
        (Set.range (deodharStandardInclusion G b.val hred b.property.1 ≫
          flagQuotientMorphism G).left)) := by
  exact transfer_partition _ _ _ (fun e => standard_quotient_range G hred e.val e.property.1)
    (deodharRichardson_cover G word hred v)
    (fun a b _ ha hb => Subtype.ext (deodharInclusion_disjoint G hred a.val b.val ha hb))

/-- Every Richardson scheme point has a unique distinguished standard-form quotient image. -/
theorem deodharStandard_unique (v : G.weylGroup) (x : (flagVariety G).scheme)
    (hx : x ∈ Set.range
      (richardsonCellInclusion G v (simpleWeylWord G.rootBase word)).left) :
    ∃! e : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
        e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v},
      x ∈ Set.range (deodharStandardInclusion G e.val hred e.property.1 ≫
        flagQuotientMorphism G).left := by
  exact unique_of_partition _ _ (deodharStandard_decomposition G hred v) x hx

private theorem standard_quotient_point (expression : Subexpression word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharStandardVariety G expression hred hd).points) :
    mapPoints (deodharInclusion G expression hred)
      (mapPoints (deodharStandardComponentIso G expression hred hd).hom x) =
        flagVarietyPointsEquiv G (flagProjection G ((reductivePointsEquiv G).symm
          (mapPoints (deodharStandardInclusion G expression hred hd) x))) := by
  have h := congrArg (fun f : (deodharStandardVariety G expression hred hd).toOver ⟶
    (flagVariety G).toOver => mapPoints f x)
      (deodharStandardComponentIso_quotient G expression hred hd)
  have hf := flagQuotientMorphism_points G ((reductivePointsEquiv G).symm
    (mapPoints (deodharStandardInclusion G expression hred hd) x))
  rw [Equiv.apply_symm_apply] at hf
  exact (mapPoints_comp (deodharStandardComponentIso G expression hred hd).hom
    (deodharInclusion G expression hred) x).symm.trans
      (h.trans ((mapPoints_comp (deodharStandardInclusion G expression hred hd)
        (flagQuotientMorphism G) x).trans hf))

/-- A component is the flag image of the ordered selected root-factor product. -/
theorem deodharComponent_products (expression : Subexpression word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    Set.range (mapPoints (deodharInclusion G expression hred)) =
      (fun g : G.points => flagVarietyPointsEquiv G (flagProjection G g)) ''
        (deodharRootProductSet G expression *
          {subwordRepresentative G expression word.length}) := by
  rw [← deodharStandard_products G expression hred hd, ← Set.range_comp]
  have hf := funext (standard_quotient_point G hred expression hd)
  change Set.range (mapPoints (deodharInclusion G expression hred)) =
    Set.range (fun x => flagVarietyPointsEquiv G (flagProjection G
      ((reductivePointsEquiv G).symm
        (mapPoints (deodharStandardInclusion G expression hred hd) x))))
  rw [← hf]
  exact ((pointsHomeomorph (deodharStandardComponentIso G expression hred hd)).surjective.range_comp
    (mapPoints (deodharInclusion G expression hred))).symm

end
end SchubertGeometry
