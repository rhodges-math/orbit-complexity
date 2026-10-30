import OrbitComplexity.ReductiveGroups.Groups.Tangents.AlgebraicTangentJordanExistence
import OrbitComplexity.ReductiveGroups.Groups.Centralizers.TorusCentralizerNormalizer
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCentralNilpotent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveTangentRadical
import OrbitComplexity.ReductiveGroups.Lie.Roots.JordanCartanCriterion

/-!
# Torus Centralizer Jordan

Jordan parts of torus-centralizing tangents remain in the
torus centralizer. Equality with the torus tangent is proved under the
geometric hypothesis that semisimple centralizing tangents are toral; for a
maximal torus this hypothesis is `maximalTorus_semisimpleCentralizer_mem_tangent`
(`Groups/MaximalTorusLieCartan.lean`). -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The tangent image of the subgroup fixed by original torus
conjugation, exposed as a Lie subalgebra. -/
abbrev torusCentralizerTangent
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) :
    LieSubalgebra K 𝔤 :=
  (TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (torusConjugationFixedHopfIdeal π)).hom).range

/-- Matrix centralizer inheritance, reflected by the faithful differential,
keeps both Jordan tangents inside the torus centralizer. -/
theorem torusCentralizer_jordan_parts_mem
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : 𝔤) (hd : d ∈ torusCentralizerTangent π) :
    ∃ dn ds : 𝔤,
      dn ∈ torusCentralizerTangent π ∧
      ds ∈ torusCentralizerTangent π ∧
      dn + ds = d ∧
      IsNilpotent (affineGroupMatrixDifferential n ρ dn) ∧
      Module.End.IsSemisimple (Matrix.toLin' (affineGroupMatrixDifferential n ρ ds)) := by
  obtain ⟨dn, ds, hsum, hn, hs, hcentral⟩ :=
    algebraicTangentJordan_exists n ρ hρ d
  let f := affineGroupMatrixDifferential n ρ
  have hf : Function.Injective f :=
    AffineGroupMatrixDifferential.injective_of_surjective n ρ hρ
  have hkeep (z : 𝔤)
      (hz : ∀ Y : Matrix (Fin n) (Fin n) K,
        Commute Y (f d) → Commute Y (f z)) :
      z ∈ torusCentralizerTangent π := by
    apply (TorusCentralizerTangent.mem_torusConjugationFixed_iff_bracket π hπ z).mpr
    intro t
    have htd : ⁅(t : 𝔤), d⁆ = 0 :=
      (TorusCentralizerTangent.mem_torusConjugationFixed_iff_bracket π hπ d).mp hd t
    have hmatrix : Commute (f (t : 𝔤)) (f d) := by
      rw [commute_iff_lie_eq, ← LieHom.map_lie, htd, map_zero]
    have hmatrix' := hz (f (t : 𝔤)) hmatrix
    apply hf
    rw [map_zero, LieHom.map_lie]
    exact (commute_iff_lie_eq).mp hmatrix'
  refine ⟨dn, ds, hkeep dn ?_, hkeep ds ?_, hsum, ?_, ?_⟩
  · intro Y hY
    simpa only [f, affineGroupMatrixDifferential_apply] using (hcentral Y hY).1
  · intro Y hY
    simpa only [f, affineGroupMatrixDifferential_apply] using (hcentral Y hY).2
  · simpa only [affineGroupMatrixDifferential_apply] using hn
  · simpa only [affineGroupMatrixDifferential_apply] using hs

/-- Conditional torus-centralizer equality for the reductive group.
The single geometric hypothesis `hsemi` requires membership in the fixed
torus only for semisimple tangents of its centralizer; it is discharged for a
maximal torus in `Groups/MaximalTorusLieCartan.lean`. -/
theorem TorusCentralizerJordan.eq_torus_of_semisimple_mem
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (hsemi : ∀ d : 𝔤, d ∈ torusCentralizerTangent π →
      Module.End.IsSemisimple (Matrix.toLin' (affineGroupMatrixDifferential n ρ d)) →
      d ∈ diagonalizableTangentImage π) :
    torusCentralizerTangent π = diagonalizableTangentImage π := by
  let H := torusCentralizerTangent π
  let T := diagonalizableTangentImage π
  let f := affineGroupMatrixDifferential n ρ
  let _ : Module.Finite K 𝔤 := finiteTypeAffineGroup_tangent_finite
  let _ : LieAlgebra.HasCentralRadical K 𝔤 :=
    reductive_tangent_hasCentralRadical hB
  have hf : Function.Injective f :=
    AffineGroupMatrixDifferential.injective_of_surjective n ρ hρ
  have hTH : T ≤ H := by
    intro x hx
    apply (TorusCentralizerTangent.mem_torusConjugationFixed_iff_bracket π hπ x).mpr
    intro y
    have : IsLieAbelian T := inferInstance
    have hbr : ⁅(y : 𝔤), x⁆ = 0 := by
      exact congrArg Subtype.val (trivial_lie_zero T T y ⟨x, hx⟩)
    exact hbr
  have hcentral : ∀ t : 𝔤, t ∈ T → ∀ y : 𝔤, y ∈ H → ⁅t, y⁆ = 0 := by
    intro t ht y hy
    exact (TorusCentralizerTangent.mem_torusConjugationFixed_iff_bracket π hπ y).mp hy ⟨t, ht⟩
  have hnorm : H.normalizer = H :=
    TorusConjugationFixed.tangentImage_normalizer π hπ
  have hparts : ∀ x : H, ∃ xn : H, ∃ xs : T,
      (xn : 𝔤) + (xs : 𝔤) = (x : 𝔤) ∧ IsNilpotent (f (xn : 𝔤)) := by
    intro x
    obtain ⟨dn, ds, hdn, hds, hsum, hnil, hss⟩ :=
      torusCentralizer_jordan_parts_mem π hπ n ρ hρ x x.property
    refine ⟨⟨dn, hdn⟩, ⟨ds, hsemi ds hds hss⟩, hsum, hnil⟩
  have hzero : ∀ z : 𝔤, z ∈ LieAlgebra.center K 𝔤 →
      IsNilpotent (f z) → z = 0 := by
    intro z hz hn
    exact ReductiveCentralNilpotent.central_matrix_nilpotent_eq_zero n ρ hρ hB z hz hn
  exact JordanCartanCriterion.cartans_equal_of_no_central_nilpotents T H hTH hcentral hnorm
    f hf hparts hzero

end ReductiveGroups

