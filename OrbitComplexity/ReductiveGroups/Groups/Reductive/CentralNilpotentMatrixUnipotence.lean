import OrbitComplexity.ReductiveGroups.Groups.Generated.CentralNilpotentGenerated
import OrbitComplexity.ReductiveGroups.Groups.Generated.RadicalGeneratedMatrixUnipotence
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentImageExponentialUnipotence

/-!
# Central Nilpotent Matrix Unipotence

One unipotence exponent works for the whole central-nilpotent generated
subgroup in any matrix representation, before and after closure. -/

noncomputable section
namespace ReductiveGroups
open WithConv

attribute [local instance 100] LieRing.ofAssociativeRing

universe u w
variable {K B : Type u} [Field K] [CharZero K]
  [CommRing B] [HopfAlgebra K B]
variable (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
  (hρ : Function.Surjective ρ)
variable (m : ℕ) (σ : TauCeti.GeneralLinear.coordinateHopfAlgebra K m →ₐc[K] B)

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

private theorem centralNilpotentPoint_matrix_word
    (g : gaGeneratedPointSubgroup (centralNilpotentGaMorphism n ρ hρ)) :
    ∃ xs : List (centralNilpotentIdeal (affineGroupMatrixDifferential n ρ)),
      representedMatrixPoint (K := K) m σ g.val =
        (xs.map (fun (d : centralNilpotentIdeal (affineGroupMatrixDifferential n ρ)) =>
          associativeExponential (K := K) (affineGroupMatrixDifferential m σ (d : 𝔤)))).prod := by
  let H := centralNilpotentIdeal (affineGroupMatrixDifferential n ρ)
  let F := representedMatrixPoint (K := K) m σ
  let D := affineGroupMatrixDifferential m σ
  have hgen (d : H) (t : Multiplicative K) :
      ∃ xs : List H, F (gaAffineGroupPoints (centralNilpotentGaMorphism n ρ hρ d) t) =
        (xs.map (fun (z : H) => associativeExponential (K := K) (D (z : 𝔤)))).prod := by
    let s : K := Multiplicative.toAdd t
    refine ⟨[s • d], ?_⟩
    have ht := GaAffineGroupPoints.matrix_eq_exponential m
      (centralNilpotentGaMorphism n ρ hρ d) σ s
    have hDs : D ((s • d : H) : 𝔤) = s • D (d : 𝔤) := by simp [D]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hDs]
    simpa [F, representedMatrixPoint, D, s, centralNilpotentGaMorphism_tangent] using ht
  have hword : ∀ g ∈ gaGeneratedPointSubgroup (centralNilpotentGaMorphism n ρ hρ),
      ∃ xs : List H, F g =
        (xs.map (fun (z : H) => associativeExponential (K := K) (D (z : 𝔤)))).prod := by
    intro z hz
    change z ∈ Subgroup.closure (⋃ d : H,
      Set.range (gaAffineGroupPoints (centralNilpotentGaMorphism n ρ hρ d))) at hz
    induction hz using Subgroup.closure_induction'' with
    | mem z hz =>
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, rfl⟩ := hd
      exact hgen d t
    | inv_mem z hz =>
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, rfl⟩ := hd
      rw [← map_inv (gaAffineGroupPoints (centralNilpotentGaMorphism n ρ hρ d)) t]
      exact hgen d t⁻¹
    | one => exact ⟨[], by simp [F]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨xs, hxs⟩ := hx
      obtain ⟨ys, hys⟩ := hy
      refine ⟨xs ++ ys, ?_⟩
      simp only [map_mul, hxs, hys, List.map_append, List.prod_append]
  exact hword g.val g.property

/-- The equality is

```lean
∃ N : ℕ, ∀ g : gaGeneratedPointSubgroup (centralNilpotentGaMorphism n ρ hρ),
      (representedMatrixPoint (K := K) m σ g.val - 1) ^ N = 0
```
-/
theorem CentralNilpotentGeneratedPoint.matrix_uniform_unipotent :
    ∃ N : ℕ, ∀ g : gaGeneratedPointSubgroup (centralNilpotentGaMorphism n ρ hρ),
      (representedMatrixPoint (K := K) m σ g.val - 1) ^ N = 0 := by
  let H := centralNilpotentIdeal (affineGroupMatrixDifferential n ρ)
  let f := (affineGroupMatrixDifferential m σ).comp H.toLieSubalgebra.incl
  have hf (x : H) : IsNilpotent (f x) := by
    change IsNilpotent (affineGroupMatrixDifferential m σ (x : 𝔤))
    have hx := gaAffineGroupTangent_matrix_nilpotent m
      (centralNilpotentGaMorphism n ρ hρ x) σ
    simpa only [centralNilpotentGaMorphism_tangent] using hx
  obtain ⟨N, hN⟩ := NilpotentImageExponentialUnipotence.exists_unipotence_of_nilpotent_images f hf
  refine ⟨N, ?_⟩
  intro g
  obtain ⟨xs, hxs⟩ := centralNilpotentPoint_matrix_word n ρ hρ m σ g
  rw [hxs]
  exact hN xs

/-- The same fixed exponent holds on every algebra-valued point of the
closed subgroup, rather than only the generating field points. -/
theorem CentralNilpotentGeneratedQuotient.matrix_uniform_unipotent :
    ∃ N : ℕ, ∀ {A : Type w} [CommRing A] [Algebra K A]
      (g : WithConv ((TauCeti.CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
        (centralNilpotentGeneratedHopfIdeal n ρ hρ)) →ₐ[K] A)),
      ((TauCeti.GeneralLinear.pointsMulEquiv m (TauCeti.AlgHom.mapDomain
        ((TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
          (centralNilpotentGeneratedHopfIdeal n ρ hρ)).hom.comp σ) g) :
            Matrix (Fin m) (Fin m) A) - 1) ^ N = 0 := by
  obtain ⟨N, hN⟩ := CentralNilpotentGeneratedPoint.matrix_uniform_unipotent n ρ hρ m σ
  refine ⟨N, ?_⟩
  intro A _ _ g
  apply GaGeneratedQuotient.matrix_pow_sub_one_eq_zero
    (centralNilpotentGaMorphism n ρ hρ) m σ N
  exact hN

end ReductiveGroups
