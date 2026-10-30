import OrbitComplexity.GroupActions.Rosenlicht.AffineOpenPoints
import OrbitComplexity.GroupActions.Rosenlicht.AffineRelationFields

/-!
# RelationPointEquations
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

private abbrev chartCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A point of a relation chart annihilates every regular polynomial relation
when its two coordinate points evaluate the coefficients and variables. -/
theorem relationChartPoint_relations (U V : X.scheme.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {ι : Type v}
    (c : ι → Γ(X.scheme, V))
    (p : (X.openSubvariety U).points) (q : (X.openSubvariety V).points)
    (r : Spec (.of K) ⟶ relationChart H X U V)
    (hfirst : r ≫ relationChartFirst H X U V = p.val)
    (hsecond : r ≫ relationChartSecond H X U V = q.val) :
    letI := relationChartAlgebra H X U V
    RingHom.ker (relationChartCoordinates H X U V c) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (affineOpenPointEval X U hU p)
        (fun a ↦ affineOpenPointEval X V hV q (c a))) := by
  let _ : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X.toSpec⟩
  let _ : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ X.toSpec⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let : Algebra K Γ(U.toScheme, ⊤) := chartCoordinateAlgebra (.of K) U.toScheme
  let : Algebra K Γ(V.toScheme, ⊤) := chartCoordinateAlgebra (.of K) V.toScheme
  let := relationChartAlgebra H X U V
  let f := relationChartCoordinates H X U V c
  let ρ : Γ(relationChart H X U V, ⊤) →+* K :=
    (r.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
  have hx (a : Γ(X.scheme, U)) :
      ρ ((relationChartFirst H X U V).appTop (U.topIso.inv a)) =
        affineOpenPointEval X U hU p a := by
    change (Scheme.ΓSpecIso (.of K)).hom
      (r.appTop ((relationChartFirst H X U V).appTop (U.topIso.inv a))) =
        ((affineSchemePointsEquiv K U.toScheme) p) (U.topIso.inv a)
    have h := congrArg (fun f : Spec (.of K) ⟶ U.toScheme ↦ f.appTop) hfirst
    rw [Scheme.Hom.comp_appTop] at h
    exact (congrArg (fun f : Γ(U.toScheme, ⊤) ⟶ Γ(Spec (.of K), ⊤) ↦
      (Scheme.ΓSpecIso (.of K)).hom (f (U.topIso.inv a))) h).trans
        (affineSchemePointsEquiv_apply K U.toScheme p (U.topIso.inv a)).symm
  have hy (a : Γ(X.scheme, V)) :
      ρ ((relationChartSecond H X U V).appTop (V.topIso.inv a)) =
        affineOpenPointEval X V hV q a := by
    change (Scheme.ΓSpecIso (.of K)).hom
      (r.appTop ((relationChartSecond H X U V).appTop (V.topIso.inv a))) =
        ((affineSchemePointsEquiv K V.toScheme) q) (V.topIso.inv a)
    have h := congrArg (fun f : Spec (.of K) ⟶ V.toScheme ↦ f.appTop) hsecond
    rw [Scheme.Hom.comp_appTop] at h
    exact (congrArg (fun f : Γ(V.toScheme, ⊤) ⟶ Γ(Spec (.of K), ⊤) ↦
      (Scheme.ΓSpecIso (.of K)).hom (f (V.topIso.inv a))) h).trans
        (affineSchemePointsEquiv_apply K V.toScheme q (V.topIso.inv a)).symm
  have he : ρ.comp f.toRingHom = MvPolynomial.eval₂Hom (affineOpenPointEval X U hU p)
      (fun a ↦ affineOpenPointEval X V hV q (c a)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change ρ (f (MvPolynomial.C a)) = _
      have hf := f.commutes a
      change f (MvPolynomial.C a) =
        (relationChartFirst H X U V).appTop (U.topIso.inv a) at hf
      rw [hf]
      exact hx a
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change ρ (f (MvPolynomial.X a)) = _
      simp only [f, relationChartCoordinates, MvPolynomial.aeval_X]
      exact hy (c a)
  intro a ha
  change MvPolynomial.eval₂Hom (affineOpenPointEval X U hU p)
    (fun a ↦ affineOpenPointEval X V hV q (c a)) a = 0
  rw [← he, RingHom.comp_apply]
  change ρ (f a) = 0
  rw [show f a = 0 from ha, map_zero]

end

end GroupActions.Variety
