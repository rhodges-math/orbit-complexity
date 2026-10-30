import OrbitComplexity.ReductiveGroups.Groups.Cells.PointFlagSpace
import OrbitComplexity.ReductiveGroups.Algebra.ProjectiveLineElimination
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates

/-!
# Rank One Sweep Closed

Completeness of the projective line, applied to a rank-one sweep in an
affine group.

Let `Y` be a Zariski-closed set of `K`-points, `y` and `x` Ga
morphisms and `n` a point such that, for `c ≠ 0`, `g y(c) ∈ Y` exactly when
`g x(c⁻¹) n ∈ Y`. Then the set of `g` for which some point `g y(c)`, or the
limit point `g n`, lies in `Y` is closed. This is the step "closed
right-B-stable `Y` has closed `Y P_s`" once the rank-one relation of the
parabolic `P_s = B ∪ B n B` is chosen; that relation is an explicit premise
here. -/

noncomputable section
namespace ReductiveGroups

open TauCeti Polynomial

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The generic point of the group, with values in `B[X]`. -/
private def genericPolynomialPoint : WithConv (B →ₐ[K] B[X]) :=
  WithConv.toConv (IsScalarTower.toAlgHom K B B[X])

/-- Specialization of `B[X]` at a `K`-point `g` and a parameter `c`. -/
private def pointParameterEval (g : WithConv (B →ₐ[K] K)) (c : K) : B[X] →ₐ[K] K :=
  (Polynomial.aeval c).comp (Polynomial.mapAlgHom g.ofConv)

private theorem pointParameterEval_apply (g : WithConv (B →ₐ[K] K)) (c : K) (p : B[X]) :
    pointParameterEval g c p = (p.map (g.ofConv : B →+* K)).eval c := by
  simp [pointParameterEval, Polynomial.mapAlgHom, Polynomial.eval_map]

private theorem mapValue_genericPolynomialPoint (g : WithConv (B →ₐ[K] K)) (c : K) :
    AlgHom.mapValue (pointParameterEval g c) (genericPolynomialPoint (K := K) (B := B)) = g := by
  apply WithConv.ofConv_injective
  ext f
  change pointParameterEval g c (Polynomial.C f) = g.ofConv f
  rw [pointParameterEval_apply]
  simp

private theorem mapValue_constantPoint (g n : WithConv (B →ₐ[K] K)) (c : K) :
    AlgHom.mapValue (pointParameterEval g c)
      (WithConv.toConv ((Algebra.ofId K B[X]).comp n.ofConv)) = n := by
  apply WithConv.ofConv_injective
  ext f
  change pointParameterEval g c (algebraMap K B[X] (n.ofConv f)) = n.ofConv f
  exact (pointParameterEval g c).commutes _

private theorem mapValue_gaPolynomialPoint (g : WithConv (B →ₐ[K] K)) (c : K)
    (y : B →ₐc[K] SymmetricAlgebra K K) :
    AlgHom.mapValue (pointParameterEval g c) (gaParameterPoint y (X : B[X])) =
      gaParameterPoint y c := by
  rw [gaParameterPoint_mapValue]
  congr 1
  rw [pointParameterEval_apply]
  simp

/-- The coordinate polynomial of `g ↦ g y(c)`. -/
private def sweepPolynomial (y : B →ₐc[K] SymmetricAlgebra K K) (f : B) : B[X] :=
  (genericPolynomialPoint (K := K) (B := B) * gaParameterPoint y (X : B[X])).ofConv f

private theorem sweepPolynomial_eval (y : B →ₐc[K] SymmetricAlgebra K K) (f : B)
    (g : WithConv (B →ₐ[K] K)) (c : K) :
    ((sweepPolynomial y f).map (g.ofConv : B →+* K)).eval c =
      (g * gaParameterPoint y c).ofConv f := by
  rw [← pointParameterEval_apply, sweepPolynomial]
  have h := congrArg (fun p : WithConv (B →ₐ[K] K) => p.ofConv f)
    (map_mul (AlgHom.mapValue (pointParameterEval g c))
      (genericPolynomialPoint (K := K) (B := B)) (gaParameterPoint y (X : B[X])))
  simp only [mapValue_genericPolynomialPoint, mapValue_gaPolynomialPoint] at h
  rw [← h]
  rfl

/-- The coordinate polynomial of `g ↦ g x(u) n`. -/
private def limitPolynomial (x : B →ₐc[K] SymmetricAlgebra K K) (n : WithConv (B →ₐ[K] K))
    (f : B) : B[X] :=
  (genericPolynomialPoint (K := K) (B := B) * gaParameterPoint x (X : B[X]) *
    WithConv.toConv ((Algebra.ofId K B[X]).comp n.ofConv)).ofConv f

private theorem limitPolynomial_eval (x : B →ₐc[K] SymmetricAlgebra K K)
    (n : WithConv (B →ₐ[K] K)) (f : B) (g : WithConv (B →ₐ[K] K)) (u : K) :
    ((limitPolynomial x n f).map (g.ofConv : B →+* K)).eval u =
      (g * gaParameterPoint x u * n).ofConv f := by
  rw [← pointParameterEval_apply, limitPolynomial]
  have hmv : AlgHom.mapValue (pointParameterEval g u)
      (genericPolynomialPoint (K := K) (B := B) * gaParameterPoint x (X : B[X]) *
        WithConv.toConv ((Algebra.ofId K B[X]).comp n.ofConv)) =
      g * gaParameterPoint x u * n := by
    rw [map_mul, map_mul, mapValue_genericPolynomialPoint, mapValue_gaPolynomialPoint,
      mapValue_constantPoint]
  rw [← hmv]
  rfl

variable [IsAlgClosed K] [Algebra.FiniteType K B]

omit [IsAlgClosed K] in
/-- A closed set of points is the common zero set of finitely many coordinate
functions. -/
theorem exists_finset_of_isClosed_points (Y : Set (WithConv (B →ₐ[K] K))) (hY : IsClosed Y) :
    ∃ s : Finset B, Y = {g | ∀ f ∈ s, g.ofConv f = 0} := by
  classical
  obtain ⟨S, rfl⟩ := (pointGroup_isClosed_iff Y).mp hY
  have hnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (IsNoetherian.noetherian (Ideal.span S))
  refine ⟨s, Set.ext fun g => ⟨fun hg f hf => hg f (hsS hf), fun hg f hf => ?_⟩⟩
  have hmem : f ∈ Ideal.span (s : Set B) := by
    rw [show Ideal.span (s : Set B) = Ideal.span S from hspan.symm]
    exact Ideal.subset_span hf
  have hker : Ideal.span (s : Set B) ≤ RingHom.ker (g.ofConv : B →+* K) := by
    rw [Ideal.span_le]
    intro a ha
    exact hg a ha
  exact hker hmem

/-- **Closedness of a rank-one sweep.** For a closed set `Y` of `K`-points,
Ga morphisms `x, y`, and a point `n` with `g y(c) ∈ Y ↔ g x(c⁻¹) n ∈ Y` for
`c ≠ 0`, the set of `g` with `g y(c) ∈ Y` for some `c`, or `g n ∈ Y`, is
closed. The proof is elimination along the projective line. -/
theorem isClosed_rankOneSweep (Y : Set (WithConv (B →ₐ[K] K))) (hY : IsClosed Y)
    (x y : B →ₐc[K] SymmetricAlgebra K K) (n : WithConv (B →ₐ[K] K))
    (hrel : ∀ (g : WithConv (B →ₐ[K] K)) (c : K), c ≠ 0 →
      (g * gaParameterPoint y c ∈ Y ↔ g * gaParameterPoint x c⁻¹ * n ∈ Y)) :
    IsClosed ({g | ∃ c : K, g * gaParameterPoint y c ∈ Y} ∪ {g | g * n ∈ Y}) := by
  classical
  obtain ⟨s, rfl⟩ := exists_finset_of_isClosed_points Y hY
  let P : s → B[X] := fun f => sweepPolynomial y f.val
  let Q : s → B[X] := fun f => limitPolynomial x n f.val
  let e : s → ℕ := fun f => (Q f).natDegree
  let R : s → B[X] := fun f => X * reflect (e f) (Q f)
  let F : s ⊕ s → B[X] := Sum.elim P R
  let d : s ⊕ s → ℕ := Sum.elim (fun f => (P f).natDegree + 1) (fun f => e f + 1)
  have hF : ∀ i, (F i).natDegree ≤ d i := by
    rintro (f | f)
    · exact Nat.le_succ _
    · change ((X : B[X]) * reflect (e f) (Q f)).natDegree ≤ e f + 1
      have h1 : ((X : B[X]) * reflect (e f) (Q f)).natDegree ≤
          (X : B[X]).natDegree + (reflect (e f) (Q f)).natDegree := Polynomial.natDegree_mul_le
      have h2 : (X : B[X]).natDegree ≤ 1 := natDegree_X_le
      have h3 : (reflect (e f) (Q f)).natDegree ≤ e f := by
        simpa [e] using (natDegree_reflect_le (N := e f) (p := Q f))
      omega
  have hclosed := isClosed_projectiveLine_affineChart (K := K) (A := B) F d hF
  have hind : IsClosed (WithConv.ofConv ⁻¹' {φ : B →ₐ[K] K |
      (∃ t : K, ∀ i, ((F i).map (φ : B →+* K)).eval t = 0) ∨
        ∀ i, φ ((F i).coeff (d i)) = 0}) := by
    let _ : TopologicalSpace (B →ₐ[K] K) := pointZariskiTopology
    exact hclosed.preimage continuous_induced_dom
  convert hind using 1
  ext g
  simp only [Set.mem_union, Set.mem_preimage]
  have hPeval (f : s) (c : K) :
      ((P f).map (g.ofConv : B →+* K)).eval c = (g * gaParameterPoint y c).ofConv f.val :=
    sweepPolynomial_eval y f.val g c
  have hQeval (f : s) (u : K) :
      ((Q f).map (g.ofConv : B →+* K)).eval u = (g * gaParameterPoint x u * n).ofConv f.val :=
    limitPolynomial_eval x n f.val g u
  have hRzero (f : s) : ((R f).map (g.ofConv : B →+* K)).eval 0 = 0 := by
    simp [R]
  have hRiff (f : s) (c : K) (hc : c ≠ 0) :
      ((R f).map (g.ofConv : B →+* K)).eval c = 0 ↔
        (g * gaParameterPoint x c⁻¹ * n).ofConv f.val = 0 := by
    let _ : Invertible c⁻¹ := invertibleOfNonzero (inv_ne_zero hc)
    have hdeg : ((Q f).map (g.ofConv : B →+* K)).natDegree ≤ e f :=
      natDegree_map_le
    have h := eval₂_reflect_eq_zero_iff (RingHom.id K) c⁻¹ (e f)
      ((Q f).map (g.ofConv : B →+* K)) hdeg
    rw [invOf_eq_inv, inv_inv] at h
    have hmul : ((R f).map (g.ofConv : B →+* K)).eval c =
        c * (reflect (e f) ((Q f).map (g.ofConv : B →+* K))).eval c := by
      simp only [R, Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X, reflect_map]
    rw [hmul, mul_eq_zero, or_iff_right hc, ← hQeval]
    exact h
  have hRlead (f : s) : g.ofConv ((R f).coeff (e f + 1)) = (g * n).ofConv f.val := by
    have hc : (R f).coeff (e f + 1) = (Q f).coeff 0 := by
      simp only [R, coeff_X_mul, coeff_reflect]
      simp [revAt_le (le_refl (e f))]
    rw [hc]
    have h0 : g.ofConv ((Q f).coeff 0) = ((Q f).map (g.ofConv : B →+* K)).eval 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
      rfl
    rw [h0, hQeval]
    have hx0 : gaParameterPoint x (0 : K) = 1 := by
      simp only [gaParameterPoint, ofAdd_zero, map_one]
    rw [hx0, mul_one]
  constructor
  · rintro (⟨c, hc⟩ | hn)
    · left
      refine ⟨c, ?_⟩
      rintro (f | f)
      · change ((P f).map (g.ofConv : B →+* K)).eval c = 0
        rw [hPeval]
        exact hc f.val f.property
      · change ((R f).map (g.ofConv : B →+* K)).eval c = 0
        by_cases hc0 : c = 0
        · subst hc0; exact hRzero f
        · exact (hRiff f c hc0).mpr (((hrel g c hc0).mp hc) f.val f.property)
    · right
      rintro (f | f)
      · change g.ofConv ((P f).coeff ((P f).natDegree + 1)) = 0
        rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), map_zero]
      · change g.ofConv ((R f).coeff (e f + 1)) = 0
        rw [hRlead]
        exact hn f.val f.property
  · rintro (⟨c, hc⟩ | hn)
    · left
      refine ⟨c, fun f hf => ?_⟩
      have := hc (Sum.inl ⟨f, hf⟩)
      change ((P ⟨f, hf⟩).map (g.ofConv : B →+* K)).eval c = 0 at this
      rwa [hPeval] at this
    · right
      intro f hf
      have := hn (Sum.inr ⟨f, hf⟩)
      change g.ofConv ((R ⟨f, hf⟩).coeff (e ⟨f, hf⟩ + 1)) = 0 at this
      rwa [hRlead] at this

end ReductiveGroups
