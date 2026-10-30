import OrbitComplexity.GroupActions.Rosenlicht.RelationFibreTests
import OrbitComplexity.GroupActions.Rosenlicht.OpenValues
import OrbitComplexity.GroupActions.Rosenlicht.OpenValueUnits
import OrbitComplexity.GroupActions.Rosenlicht.AffineGenerators
import OrbitComplexity.GroupActions.Rosenlicht.OrbitClosureFibres
import OrbitComplexity.GroupActions.Rosenlicht.OrbitClosures

/-!
# Finite invariant functions separating orbits
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

private abbrev chartCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A finite family of invariant regular functions separates algebraic-group
orbits on a nonempty open subset. -/
theorem exists_open_orbit_separators :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ U : X.scheme.Opens, ∃ hUa : IsAffineOpen U, ∃ hU : genericPoint X.scheme ∈ U,
      letI : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
      ∃ S : Finset Γ(X.scheme, U),
        (∀ a ∈ S, X.scheme.germToFunctionField U a ∈ invariantField H X) ∧
        ∃ W : X.scheme.Opens, (W : Set X.scheme).Nonempty ∧ ∃ hWU : W ≤ U,
          ∀ (x y : X.points) (hx : X.pointMap x ∈ W) (hy : X.pointMap y ∈ W),
            (∀ a ∈ S, regularValue X U hUa x (hWU hx) a =
              regularValue X U hUa y (hWU hy) a) → y ∈ MulAction.orbit H.points x := by
  classical
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  obtain ⟨V, hVa, hV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X.scheme ∈ (⊤ : X.scheme.Opens) from trivial)
  have : Nonempty V := ⟨⟨genericPoint X.scheme, hV⟩⟩
  let _ : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ X.toSpec⟩
  have : IsAffine V.toScheme := hVa
  let : Algebra K Γ(V.toScheme, ⊤) := chartCoordinateAlgebra (.of K) V.toScheme
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of K)) := by
    change LocallyOfFiniteType (V.ι ≫ X.toSpec)
    exact (X.openSubvariety V).locallyOfFiniteType
  obtain ⟨m, c, hc⟩ := exists_affine_generators K V.toScheme
  obtain ⟨U, hUa, hU, s, d, hd, hcoeff, htest⟩ :=
    exists_relationFibre_tests H X V hVa m c hc
  have : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
  let S := s.biUnion (fun p ↦ p.support.image p.coeff)
  obtain ⟨O, hO, hclosure⟩ := exists_open_orbitClosure_fibres H X
  have hηO : genericPoint X.scheme ∈ O :=
    ((genericPoint_spec X.scheme).mem_open_set_iff O.isOpen).mpr (by simpa using hO)
  have hηd : genericPoint X.scheme ∈ X.scheme.basicOpen d := by
    rw [Scheme.mem_basicOpen X.scheme d (genericPoint X.scheme) hU, isUnit_iff_ne_zero]
    intro hz
    apply hd
    apply X.scheme.germToFunctionField_injective U
    simpa only [map_zero] using hz
  let W := U ⊓ V ⊓ X.scheme.basicOpen d ⊓ O
  have hηW : genericPoint X.scheme ∈ W := ⟨⟨⟨hU, hV⟩, hηd⟩, hηO⟩
  have hWU : W ≤ U := fun _ hx ↦ hx.1.1.1
  have hWV : W ≤ V := fun _ hx ↦ hx.1.1.2
  refine ⟨U, hUa, hU, S, ?_, W, ⟨genericPoint X.scheme, hηW⟩, hWU, ?_⟩
  · intro a ha
    obtain ⟨p, hp, ha⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact hcoeff p hp n
  · intro x y hx hy he
    let px := pointInOpen X U x (hWU hx)
    let py := pointInOpen X U y (hWU hy)
    let qx := pointInOpen X V x (hWV hx)
    let qy := pointInOpen X V y (hWV hy)
    have hxU : mapPoints (X.openInclusion U) px = x := mapPoints_pointInOpen X U x _
    have hyU : mapPoints (X.openInclusion U) py = y := mapPoints_pointInOpen X U y _
    have hxV : mapPoints (X.openInclusion V) qx = x := mapPoints_pointInOpen X V x _
    have hyV : mapPoints (X.openInclusion V) qy = y := mapPoints_pointInOpen X V y _
    have hdx : IsUnit (affineOpenPointEval X U hUa px d) := by
      apply affineOpenPointEval_isUnit X U hUa px d
      rw [hxU]
      exact hx.1.2
    have hdy : IsUnit (affineOpenPointEval X U hUa py d) := by
      apply affineOpenPointEval_isUnit X U hUa py d
      rw [hyU]
      exact hy.1.2
    have he' (p) (hp : p ∈ s) (n : Fin m →₀ ℕ) :
        affineOpenPointEval X U hUa px (p.coeff n) =
          affineOpenPointEval X U hUa py (p.coeff n) := by
      by_cases hn : n ∈ p.support
      · exact he (p.coeff n) (Finset.mem_biUnion.mpr
          ⟨p, hp, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩)
      · rw [MvPolynomial.notMem_support_iff.mp hn, map_zero, map_zero]
    obtain ⟨hxy, hyx⟩ := htest px py qx qy (hxU.trans hxV.symm)
      (hyU.trans hyV.symm) hdx hdy he'
    rw [hxU, hyU] at hxy hyx
    apply GroupActions.mem_orbit_of_mutual_closure H X x y
    · rw [hclosure y hy.2]
      exact hxy
    · rw [hclosure x hx.2]
      exact hyx

end

end GroupActions.Variety
