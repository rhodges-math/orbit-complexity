import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusSemisimpleDiagonalization
import OrbitComplexity.ReductiveGroups.Lie.Roots.MatrixBasisConjugation

/-!
# Torus Semisimple Common Basis

A common eigenbasis for a split-torus matrix representation and
one commuting semisimple tangent matrix. -/

noncomputable section
namespace ReductiveGroups
open Module

variable {K G : Type*} [Field K] [IsAlgClosed K] [CommGroup G]

omit [IsAlgClosed K] in
private theorem torusPoints_mul_comm
    (g h : WithConv (MonoidAlgebra K G →ₐ[K] K)) :
    g * h = h * g := by
  apply (TauCeti.DiagonalizableGroup.pointsMulEquiv
    (R := K) (A := K) (G := G)).injective
  simp only [map_mul]
  exact mul_comm
    (TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K) (A := K) (G := G) g)
    (TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K) (A := K) (G := G) h)

omit [IsAlgClosed K] in
private theorem toMatrix_diagonal_of_eigenbasis
    {n : ℕ} (b : Basis (Fin n) K (Fin n → K))
    (f : Module.End K (Fin n → K))
    (hf : ∀ j : Fin n, ∃ ξ : K, f (b j) = ξ • b j) :
    ∃ v : Fin n → K, LinearMap.toMatrix b b f = Matrix.diagonal v := by
  choose v hv using hf
  refine ⟨v, ?_⟩
  ext i j
  rw [LinearMap.toMatrix_apply, hv j]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij]

omit [IsAlgClosed K] in
private theorem torusPointMatrices_commute
    (n : ℕ)
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K G)
    (g h : WithConv (MonoidAlgebra K G →ₐ[K] K)) :
    Commute
      (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain q g) : Matrix (Fin n) (Fin n) K)
      (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain q h) : Matrix (Fin n) (Fin n) K) := by
  have hgh := torusPoints_mul_comm g h
  have hmap := congrArg (TauCeti.AlgHom.mapDomain q) hgh
  have hmat := congrArg (TauCeti.GeneralLinear.pointsMulEquiv n) hmap
  change
    (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain q g) :
      Matrix (Fin n) (Fin n) K) *
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain q h) :
        Matrix (Fin n) (Fin n) K) = _
  have hv := congrArg
    (fun z : Matrix.GeneralLinearGroup (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hmat
  simpa only [map_mul, Matrix.GeneralLinearGroup.coe_mul] using hv

omit [IsAlgClosed K] in
private theorem torusPointMatrix_isSemisimple
    (n : ℕ)
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K G)
    (g : WithConv (MonoidAlgebra K G →ₐ[K] K)) :
    Module.End.IsSemisimple
      (Matrix.toLin'
        (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain q g) : Matrix (Fin n) (Fin n) K)) := by
  have hs := torusMatrixPoint_isSemisimple K G n q g.ofConv
  have hpt : (TauCeti.GeneralLinear.genericMatrix K n).map
      (g.ofConv.comp (q : _ →ₐ[K] _)) =
        (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain q g) : Matrix (Fin n) (Fin n) K) := by
    rw [TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
    rfl
  rwa [hpt] at hs

/-- A split-torus matrix representation and a commuting semisimple matrix
have one common finite basis. The conclusion concerns the matrices
of all torus points, not a diagonalizable family. -/
theorem exists_torusSemisimple_commonBasis
    (n : ℕ)
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K G)
    (Xs : Matrix (Fin n) (Fin n) K)
    (hs : Module.End.IsSemisimple (Matrix.toLin' Xs))
    (hcomm : ∀ g : WithConv (MonoidAlgebra K G →ₐ[K] K),
      Commute
        (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain q g) : Matrix (Fin n) (Fin n) K)
        Xs) :
    ∃ b : Basis (Fin n) K (Fin n → K),
      (∀ g : WithConv (MonoidAlgebra K G →ₐ[K] K),
        ∃ v : Fin n → K,
          LinearMap.toMatrix b b (Matrix.toLin'
            (TauCeti.GeneralLinear.pointsMulEquiv n
              (TauCeti.AlgHom.mapDomain q g) : Matrix (Fin n) (Fin n) K)) =
            Matrix.diagonal v) ∧
      (∃ v : Fin n → K,
        LinearMap.toMatrix b b (Matrix.toLin' Xs) = Matrix.diagonal v) := by
  let F : Sum (WithConv (MonoidAlgebra K G →ₐ[K] K)) Unit →
      Module.End K (Fin n → K)
    | .inl g => Matrix.toLin'
        (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain q g) : Matrix (Fin n) (Fin n) K)
    | .inr _ => Matrix.toLin' Xs
  have hFsemi (i : Sum (WithConv (MonoidAlgebra K G →ₐ[K] K)) Unit) :
      Module.End.IsSemisimple (F i) := by
    cases i with
    | inl g => exact torusPointMatrix_isSemisimple n q g
    | inr _ => exact hs
  have hFcomm : Pairwise fun i j => Commute (F i) (F j) := by
    intro i j hij
    cases i with
    | inl g =>
      cases j with
      | inl h =>
        exact (torusPointMatrices_commute n q g h).map
          (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
            Module.End K (Fin n → K))
      | inr _ =>
        exact (hcomm g).map
          (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
            Module.End K (Fin n → K))
    | inr _ =>
      cases j with
      | inl g =>
        exact ((hcomm g).symm).map
          (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
            Module.End K (Fin n → K))
      | inr _ => exact Commute.refl _
  obtain ⟨t, b, hb⟩ := exists_simultaneous_eigenbasis F hFcomm hFsemi
  have _ : Finite t := Module.Finite.finite_basis b
  let _ : Fintype t := Fintype.ofFinite t
  have hcard : Fintype.card t = n := by
    have ht := Module.finrank_eq_card_basis b
    simpa using ht.symm
  let e : t ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b' : Basis (Fin n) K (Fin n → K) := b.reindex e
  have hb' (j : Fin n) :
      ∃ χ : Sum (WithConv (MonoidAlgebra K G →ₐ[K] K)) Unit → K,
        ∀ i, F i (b' j) = χ i • b' j := by
    simpa only [b', Basis.reindex_apply] using hb (e.symm j)
  refine ⟨b', ?_, ?_⟩
  · intro g
    apply toMatrix_diagonal_of_eigenbasis b'
    intro j
    obtain ⟨χ, hχ⟩ := hb' j
    exact ⟨χ (.inl g), hχ (.inl g)⟩
  · apply toMatrix_diagonal_of_eigenbasis b'
    intro j
    obtain ⟨χ, hχ⟩ := hb' j
    exact ⟨χ (.inr ()), hχ (.inr ())⟩

end ReductiveGroups
