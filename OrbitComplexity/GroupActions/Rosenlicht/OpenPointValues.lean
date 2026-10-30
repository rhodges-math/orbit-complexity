import OrbitComplexity.GroupActions.Rosenlicht.OpenValues

/-!
# Evaluation on open subvarieties

Evaluation of regular sections commutes with morphisms and restriction to smaller open
subsets.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

private abbrev chartCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

variable {K : Type u} [Field K] (X Y : GroupActions.Variety K)

/-- Pullback along a rational point evaluates sections on any open subset. -/
def openPointEval (U : X.scheme.Opens) (p : (X.openSubvariety U).points) :
    Γ(X.scheme, U) →+* K :=
  (U.topIso.inv ≫ p.val.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom

/-- On an affine open, evaluation by affine coordinates equals pullback along
the rational point. -/
theorem affineOpenPointEval_eq_open (U : X.scheme.Opens) (hU : IsAffineOpen U)
    (p : (X.openSubvariety U).points) :
    affineOpenPointEval X U hU p = openPointEval X U p := by
  let _ : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X.toSpec⟩
  have : IsAffine U.toScheme := hU
  let : Algebra K Γ(U.toScheme, ⊤) := chartCoordinateAlgebra (.of K) U.toScheme
  ext a
  exact affineSchemePointsEquiv_apply K U.toScheme p (U.topIso.inv a)

/-- Section evaluation commutes with pullback along morphisms between open
subschemes at compatible rational points. -/
theorem openPointEval_comp (U : X.scheme.Opens) (V : Y.scheme.Opens)
    (f : U.toScheme ⟶ V.toScheme)
    (p : (X.openSubvariety U).points) (q : (Y.openSubvariety V).points)
    (hpq : p.val ≫ f = q.val) (a : Γ(Y.scheme, V)) :
    openPointEval X U p (U.topIso.hom (f.appTop (V.topIso.inv a))) =
      openPointEval Y V q a := by
  change (Scheme.ΓSpecIso (.of K)).hom
      (p.val.appTop (U.topIso.inv (U.topIso.hom (f.appTop (V.topIso.inv a))))) = _
  rw [show U.topIso.inv (U.topIso.hom (f.appTop (V.topIso.inv a))) =
    f.appTop (V.topIso.inv a) from U.topIso.commRingCatIsoToRingEquiv.left_inv _]
  let p' : Spec (.of K) ⟶ U.toScheme := p.val
  let q' : Spec (.of K) ⟶ V.toScheme := q.val
  have hpq' : p' ≫ f = q' := hpq
  have h := congrArg (fun f : Spec (.of K) ⟶ V.toScheme ↦ f.appTop) hpq'
  rw [Scheme.Hom.comp_appTop] at h
  exact congrArg (fun g : Γ(V.toScheme, ⊤) ⟶ Γ(Spec (.of K), ⊤) ↦
    (Scheme.ΓSpecIso (.of K)).hom (g (V.topIso.inv a))) h

private theorem homOfLE_sections {U W : X.scheme.Opens} (e : W ≤ U) :
    U.topIso.inv ≫ (X.scheme.homOfLE e).appTop ≫ W.topIso.hom =
      X.scheme.presheaf.map (homOfLE e).op := by
  rw [Scheme.homOfLE_appTop]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv]
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Restriction of a regular section preserves its evaluation at compatible
rational points of nested open subsets. -/
theorem openPointEval_res (U W : X.scheme.Opens) (e : W ≤ U)
    (p : (X.openSubvariety W).points) (q : (X.openSubvariety U).points)
    (hpq : p.val ≫ X.scheme.homOfLE e = q.val) (a : Γ(X.scheme, U)) :
    openPointEval X W p (X.scheme.presheaf.map (homOfLE e).op a) =
      openPointEval X U q a := by
  have h := openPointEval_comp X X W U (X.scheme.homOfLE e) p q hpq a
  have hs : W.topIso.hom ((X.scheme.homOfLE e).appTop (U.topIso.inv a)) =
      X.scheme.presheaf.map (homOfLE e).op a :=
    congrArg (fun f : Γ(X.scheme, U) ⟶ Γ(X.scheme, W) ↦ f a) (homOfLE_sections X e)
  rw [hs] at h
  exact h

/-- Restriction to a smaller affine open preserves the value of a regular
section at any rational point lying in that smaller open. -/
theorem regularValue_res (U W : X.scheme.Opens) (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (e : W ≤ U) (x : X.points) (hx : X.pointMap x ∈ W)
    (a : Γ(X.scheme, U)) :
    regularValue X W hW x hx (X.scheme.presheaf.map (homOfLE e).op a) =
      regularValue X U hU x (e hx) a := by
  let p := pointInOpen X W x hx
  let q := pointInOpen X U x (e hx)
  let p' : Spec (.of K) ⟶ W.toScheme := p.val
  let q' : Spec (.of K) ⟶ U.toScheme := q.val
  have hp : p' ≫ W.ι = x.val :=
    congrArg Subtype.val (mapPoints_pointInOpen X W x hx)
  have hq : q' ≫ U.ι = x.val :=
    congrArg Subtype.val (mapPoints_pointInOpen X U x (e hx))
  have hpq : p' ≫ X.scheme.homOfLE e = q' := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, hp, hq]
  change affineOpenPointEval X W hW p _ = affineOpenPointEval X U hU q a
  rw [affineOpenPointEval_eq_open, affineOpenPointEval_eq_open]
  exact openPointEval_res X U W e p q hpq a

end

end GroupActions.Variety
