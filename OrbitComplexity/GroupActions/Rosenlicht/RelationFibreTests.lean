import OrbitComplexity.GroupActions.Rosenlicht.RelationChartPoints
import OrbitComplexity.GroupActions.Rosenlicht.DiagonalRelations
import OrbitComplexity.GroupActions.Rosenlicht.RelationPairFibres
import OrbitComplexity.GroupActions.Rosenlicht.OrbitRelationPoints

/-!
# RelationFibreTests
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

private abbrev chartCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

private theorem eval₂_eq_of_coeffs {R C : Type u} {ι : Type v} [CommRing R] [CommRing C]
    (f g : R →+* C) (p : MvPolynomial ι R) (y : ι → C)
    (h : ∀ n, f (p.coeff n) = g (p.coeff n)) :
    MvPolynomial.eval₂Hom f y p = MvPolynomial.eval₂Hom g y p := by
  have he : MvPolynomial.map f p = MvPolynomial.map g p := by
    ext n
    simp only [MvPolynomial.coeff_map, h]
  change p.eval₂ f y = p.eval₂ g y
  rw [MvPolynomial.eval₂_eq_eval_map, MvPolynomial.eval₂_eq_eval_map, he]

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- Finitely many invariant regular coefficients determine both ordinary
relation-fibre memberships on a pair of affine coordinate charts. -/
theorem exists_relationFibre_tests (V : X.scheme.Opens) (hV : IsAffineOpen V)
    [Nonempty V] (m : ℕ) (c : Fin m → Γ(V.toScheme, ⊤))
    (hc : letI : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ X.toSpec⟩
      letI : IsAffine V.toScheme := hV
      letI : Algebra K Γ(V.toScheme, ⊤) := chartCoordinateAlgebra (.of K) V.toScheme
      Algebra.adjoin K (Set.range c) = ⊤) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ U : X.scheme.Opens, ∃ hUa : IsAffineOpen U, ∃ hU : genericPoint X.scheme ∈ U,
      letI : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
      ∃ s : Finset (MvPolynomial (Fin m) Γ(X.scheme, U)), ∃ d : Γ(X.scheme, U),
        d ≠ 0 ∧
        (∀ p ∈ s, ∀ n : Fin m →₀ ℕ,
          X.scheme.germToFunctionField U (p.coeff n) ∈ invariantField H X) ∧
        ∀ (p₁ p₂ : (X.openSubvariety U).points)
          (q₁ q₂ : (X.openSubvariety V).points),
          mapPoints (X.openInclusion U) p₁ = mapPoints (X.openInclusion V) q₁ →
          mapPoints (X.openInclusion U) p₂ = mapPoints (X.openInclusion V) q₂ →
          IsUnit (affineOpenPointEval X U hUa p₁ d) →
          IsUnit (affineOpenPointEval X U hUa p₂ d) →
          (∀ p ∈ s, ∀ n : Fin m →₀ ℕ,
            affineOpenPointEval X U hUa p₁ (p.coeff n) =
              affineOpenPointEval X U hUa p₂ (p.coeff n)) →
          X.pointMap (mapPoints (X.openInclusion U) p₁) ∈ Set.range
            (relationFibreMap H X (mapPoints (X.openInclusion U) p₂)) ∧
          X.pointMap (mapPoints (X.openInclusion U) p₂) ∈ Set.range
            (relationFibreMap H X (mapPoints (X.openInclusion U) p₁)) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let c' : Fin m → Γ(X.scheme, V) := fun i ↦ V.topIso.hom (c i)
  obtain ⟨U, hUa, hU, s, d, hd, hcoeff, htest⟩ :=
    exists_orbitRelation_tests H X V m c'
  have : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
  let := relationChartAlgebra H X U V
  refine ⟨U, hUa, hU, s, d, hd, hcoeff, ?_⟩
  intro p₁ p₂ q₁ q₂ he₁ he₂ hd₁ hd₂ he
  let ex := affineOpenPointEval X U hUa p₁
  let ey := affineOpenPointEval X U hUa p₂
  let zx : Fin m → K := fun i ↦ affineOpenPointEval X V hV q₁ (c' i)
  let zy : Fin m → K := fun i ↦ affineOpenPointEval X V hV q₂ (c' i)
  have hdiag₁ := relationChart_diagonal_relations H X U V hUa hV c' p₁ q₁ he₁
  have hdiag₂ := relationChart_diagonal_relations H X U V hUa hV c' p₂ q₂ he₂
  have hgen₁ : ∀ p ∈ s, MvPolynomial.eval₂Hom ex zx p = 0 :=
    (htest K ex hd₁ zx).mp (fun _ hp ↦ hdiag₁ hp)
  have hgen₂ : ∀ p ∈ s, MvPolynomial.eval₂Hom ey zy p = 0 :=
    (htest K ey hd₂ zy).mp (fun _ hp ↦ hdiag₂ hp)
  have hcross₁ : ∀ p ∈ RingHom.ker (relationChartCoordinates H X U V c'),
      MvPolynomial.eval₂Hom ey zx p = 0 := by
    apply (htest K ey hd₂ zx).mpr
    intro p hp
    exact (eval₂_eq_of_coeffs ex ey p zx (he p hp)).symm.trans (hgen₁ p hp)
  have hcross₂ : ∀ p ∈ RingHom.ker (relationChartCoordinates H X U V c'),
      MvPolynomial.eval₂Hom ex zy p = 0 := by
    apply (htest K ex hd₁ zy).mpr
    intro p hp
    exact (eval₂_eq_of_coeffs ex ey p zy (he p hp)).trans (hgen₂ p hp)
  obtain ⟨r₁, hr₁, hs₁⟩ := relationChartPoint_exists H X U V hUa hV c hc p₂ q₁
    (fun _ hp ↦ hcross₁ _ hp)
  obtain ⟨r₂, hr₂, hs₂⟩ := relationChartPoint_exists H X U V hUa hV c hc p₁ q₂
    (fun _ hp ↦ hcross₂ _ hp)
  constructor
  · rw [he₁]
    exact relationFibre_mem_of_chartPoint H X U V p₂ q₁ r₁ hr₁ hs₁
  · rw [he₂]
    exact relationFibre_mem_of_chartPoint H X U V p₁ q₂ r₂ hr₂ hs₂

end

end GroupActions.Variety
