import OrbitComplexity.GroupActions.Rosenlicht.ClosedProductPoints
import OrbitComplexity.GroupActions.Rosenlicht.AffineOpenPoints
import OrbitComplexity.GroupActions.Rosenlicht.AffineRelationFields

/-!
# RelationChartPoints
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

/-- A pair of points in affine coordinate charts lifts to the relation chart
when its evaluations annihilate the full regular relation ideal. -/
theorem relationChartPoint_exists (U V : X.scheme.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {ι : Type v}
    (c : ι → Γ(V.toScheme, ⊤))
    (hc : letI : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ X.toSpec⟩
      letI : IsAffine V.toScheme := hV
      letI : Algebra K Γ(V.toScheme, ⊤) := chartCoordinateAlgebra (.of K) V.toScheme
      Algebra.adjoin K (Set.range c) = ⊤)
    (p : (X.openSubvariety U).points) (q : (X.openSubvariety V).points)
    (hrel : letI := relationChartAlgebra H X U V
      RingHom.ker (relationChartCoordinates H X U V (fun a ↦ V.topIso.hom (c a))) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (affineOpenPointEval X U hU p)
          (fun a ↦ affineOpenPointEval X V hV q (V.topIso.hom (c a))))) :
    ∃ r : Spec (.of K) ⟶ relationChart H X U V,
      r ≫ relationChartFirst H X U V = p.val ∧
      r ≫ relationChartSecond H X U V = q.val := by
  let _ : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X.toSpec⟩
  let _ : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ X.toSpec⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let : Algebra K Γ(U.toScheme, ⊤) := chartCoordinateAlgebra (.of K) U.toScheme
  let : Algebra K Γ(V.toScheme, ⊤) := chartCoordinateAlgebra (.of K) V.toScheme
  let := relationChartAlgebra H X U V
  let f := relationChartCoordinates H X U V (fun a ↦ V.topIso.hom (c a))
  let ψ := MvPolynomial.map (σ := ι) U.topIso.hom.hom
  let g := MvPolynomial.eval₂Hom (relationChartFirst H X U V).appTop.hom
    (fun a ↦ (relationChartSecond H X U V).appTop (c a))
  have he : f.toRingHom.comp ψ = g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [ψ, g, RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      change f (MvPolynomial.C (U.topIso.hom a)) =
        (relationChartFirst H X U V).appTop a
      have hf := f.commutes (U.topIso.hom a)
      change f (MvPolynomial.C (U.topIso.hom a)) =
        (relationChartFirst H X U V).appTop (U.topIso.inv (U.topIso.hom a)) at hf
      rw [show U.topIso.inv (U.topIso.hom a) = a from
        U.topIso.commRingCatIsoToRingEquiv.left_inv a] at hf
      exact hf
    · intro a
      simp only [ψ, g, RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
      change f (MvPolynomial.X a) = (relationChartSecond H X U V).appTop (c a)
      simp only [f, relationChartCoordinates, MvPolynomial.aeval_X]
      rw [show V.topIso.inv (V.topIso.hom (c a)) = c a from
        V.topIso.commRingCatIsoToRingEquiv.left_inv (c a)]
  let x := (affineSchemePointsEquiv K U.toScheme) p
  let y := (affineSchemePointsEquiv K V.toScheme) q
  have hx : (affineOpenPointEval X U hU p).comp U.topIso.hom.hom = x.toRingHom := by
    ext a
    change x (U.topIso.inv (U.topIso.hom a)) = x a
    rw [show U.topIso.inv (U.topIso.hom a) = a from
      U.topIso.commRingCatIsoToRingEquiv.left_inv a]
  have hy (a : ι) : affineOpenPointEval X V hV q (V.topIso.hom (c a)) = y (c a) := by
    change y (V.topIso.inv (V.topIso.hom (c a))) = y (c a)
    rw [show V.topIso.inv (V.topIso.hom (c a)) = c a from
      V.topIso.commRingCatIsoToRingEquiv.left_inv (c a)]
  apply @closedProductPoint_exists K inferInstance U.toScheme V.toScheme
    inferInstance inferInstance hU hV (relationChart H X U V)
    (relationChartProduct H X U V) (relationChartProduct_closed H X U V) ι c hc p q
  change RingHom.ker g ≤ RingHom.ker (MvPolynomial.eval₂Hom x.toRingHom (fun a ↦ y (c a)))
  intro a ha
  have ha' : ψ a ∈ RingHom.ker f := by
    change f (ψ a) = 0
    change (f.toRingHom.comp ψ) a = 0
    rw [he]
    exact ha
  have hz := hrel ha'
  change MvPolynomial.eval₂Hom (affineOpenPointEval X U hU p)
    (fun a ↦ affineOpenPointEval X V hV q (V.topIso.hom (c a)))
      (MvPolynomial.map U.topIso.hom.hom a) = 0 at hz
  rw [MvPolynomial.eval₂Hom_map_hom, hx] at hz
  apply RingHom.mem_ker.mpr
  simpa only [hy] using hz

end

end GroupActions.Variety
