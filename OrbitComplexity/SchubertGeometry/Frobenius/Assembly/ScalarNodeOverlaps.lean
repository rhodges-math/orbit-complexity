import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveCharts
import Mathlib.AlgebraicGeometry.Gluing
import Batteries.Tactic.Lint

/-! # Covers of scalar node intersections by refinements

The original locally directed cocone identifies the common refinements of
two points. Cartesian scalar nodes lift those refinements to the prescribed
scalar target and cover the intersection by the given transition maps.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SchubertGeometry

private theorem cocone_common_point {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    (D : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (D.map f)]
    [(D ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone D) (hc : IsColimit c) {i j : J} (x : D.obj i) (y : D.obj j)
    (h : c.ι.app i x = c.ι.app j y) :
    ∃ (k : J) (fi : k ⟶ i) (fj : k ⟶ j) (z : D.obj k), D.map fi z = x ∧ D.map fj z = y := by
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit D)
  have hi := IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit D) i
  have hj := IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit D) j
  have hi' : e.hom (c.ι.app i x) = colimit.ι D i x :=
    congrArg (fun f : D.obj i ⟶ colimit D => f x) hi
  have hj' : e.hom (c.ι.app j y) = colimit.ι D j y :=
    congrArg (fun f : D.obj j ⟶ colimit D => f y) hj
  exact (Scheme.IsLocallyDirected.ι_eq_ι_iff D).mp
    (hi'.symm.trans ((congrArg e.hom h).trans hj'))

section Overlap

variable {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    (D : Jᵒᵖ ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (D.map f)]
    [(D ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone D) (hc : IsColimit c) {Y : Scheme.{u}} (q : Y ⟶ c.pt)
    (P : J → Scheme.{u}) (r : ∀ s, P s ⟶ D.obj (op s)) (K : ∀ s, P s ⟶ Y)
    [∀ s, IsOpenImmersion (K s)]
    (hcart : ∀ s, IsPullback (r s) (K s) (c.ι.app (op s)) q)
    (g : ∀ {s t : J}, (s ⟶ t) → (P t ⟶ P s))
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion (g f)]
    (hg : ∀ {s t} (f : s ⟶ t), g f ≫ K s = K t)
    (s t : J)

private abbrev overlapIndex : Type u := Σ z : J, (s ⟶ z) × (t ⟶ z)

private def overlapMap (a : overlapIndex s t) : P a.1 ⟶ pullback (K s) (K t) :=
  pullback.lift (g a.2.1) (g a.2.2) ((hg a.2.1).trans (hg a.2.2).symm)

omit [Quiver.IsThin J] in
private theorem overlapMap_open (a : overlapIndex s t) :
    IsOpenImmersion (overlapMap P K g hg s t a) := by
  have h : overlapMap P K g hg s t a ≫ pullback.fst (K s) (K t) = g a.2.1 :=
    pullback.lift_fst _ _ _
  let : IsOpenImmersion (overlapMap P K g hg s t a ≫ pullback.fst (K s) (K t)) := by
    rw [h]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (K s) (K t))

omit [∀ {s t} (f : s ⟶ t), IsOpenImmersion (g f)] in
include D c hc q r hcart in
private theorem overlapMap_covers (x : (pullback (K s) (K t) : Scheme.{u})) :
    ∃ a : overlapIndex s t, ∃ z : P a.1, overlapMap P K g hg s t a z = x := by
  let xs := pullback.fst (K s) (K t) x
  let xt := pullback.snd (K s) (K t) x
  have hx : K s xs = K t xt :=
    congrArg (fun f : pullback (K s) (K t) ⟶ Y => f x)
      (pullback.condition (f := K s) (g := K t))
  have hs : c.ι.app (op s) (r s xs) = q (K s xs) :=
    congrArg (fun f : P s ⟶ c.pt => f xs) (hcart s).w
  have ht : c.ι.app (op t) (r t xt) = q (K t xt) :=
    congrArg (fun f : P t ⟶ c.pt => f xt) (hcart t).w
  obtain ⟨a, fi, fj, z, hzi, _hzj⟩ := cocone_common_point D c hc (r s xs) (r t xt)
    (hs.trans ((congrArg q hx).trans ht.symm))
  have hleg : c.ι.app a z = c.ι.app (op s) (D.map fi z) :=
    (congrArg (fun f : D.obj a ⟶ c.pt => f z) (c.w fi)).symm
  have hz : c.ι.app (op a.unop) z = q (K s xs) :=
    hleg.trans ((congrArg (c.ι.app (op s)) hzi).trans hs)
  obtain ⟨w, _hwr, hw⟩ := Scheme.exists_preimage_of_isPullback
    (hcart a.unop) z (K s xs) hz
  let ai : overlapIndex s t := ⟨a.unop, fi.unop, fj.unop⟩
  have hgi : g fi.unop w = xs := by
    apply (K s).injective
    have h := congrArg (fun f : P a.unop ⟶ Y => f w) (hg fi.unop)
    exact h.trans hw
  refine ⟨ai, w, ?_⟩
  apply (pullback.fst (K s) (K t)).injective
  have he := congrArg (fun f : P a.unop ⟶ P s => f w)
    (pullback.lift_fst (g fi.unop) (g fj.unop)
      ((hg fi.unop).trans (hg fj.unop).symm))
  exact he.trans hgi

/-- The specified scalar transitions cover the intersection of two scalar
nodes, using the common refinements of the original locally directed cocone. -/
def scalarNodeOverlapCover : (pullback (K s) (K t)).OpenCover.{u} :=
  Scheme.Cover.mkOfCovers (overlapIndex s t) (fun a => P a.1)
    (overlapMap P K g hg s t) (overlapMap_covers D c hc q P r K hcart g hg s t)
    (overlapMap_open P K g hg s t)

/-- Each overlap-cover arrow preserves its prescribed first transition. -/
theorem scalarNodeOverlapCover_fst (a : (scalarNodeOverlapCover D c hc q P r K hcart g hg s t).I₀) :
    (scalarNodeOverlapCover D c hc q P r K hcart g hg s t).f a ≫
      pullback.fst (K s) (K t) = g a.2.1 :=
  pullback.lift_fst _ _ _

/-- Each overlap-cover arrow preserves its prescribed second transition. -/
theorem scalarNodeOverlapCover_snd (a : (scalarNodeOverlapCover D c hc q P r K hcart g hg s t).I₀) :
    (scalarNodeOverlapCover D c hc q P r K hcart g hg s t).f a ≫
      pullback.snd (K s) (K t) = g a.2.2 :=
  pullback.lift_snd _ _ _

end Overlap
end SchubertGeometry
