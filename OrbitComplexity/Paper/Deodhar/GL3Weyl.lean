import OrbitComplexity.Paper.Deodhar.GL3Subwords
import OrbitComplexity.ReductiveGroups.GLn.MaximalTorus
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupWeylQuotient
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.LongestCount
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# Permutations of the rank-three Weyl group

Matrix representatives identify the adjacent simple reflections with transpositions.
-/

open ReductiveGroups TauCeti TauCeti.GeneralLinear WithConv
open ReductiveGroups.GLn
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

private instance units_nontrivial : Nontrivial Kˣ := by
  refine ⟨⟨1, -1, ?_⟩⟩
  intro h
  have hv := congrArg (fun a : Kˣ => (a : K)) h
  norm_num at hv

omit [CharZero K] in
private theorem torus_matrix_iff (g : (GLn.groupData K 3).points) :
    g ∈ (GLn.groupData K 3).torusPoints ↔
      pointsMulEquiv (R := K) (A := K) 3 g ∈ TauCeti.diagonalTorus K 3 := by
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := (ReductiveGroups.mem_torusPoints_iff
      (GLn.groupData K 3).torusIdeal (GLn.groupData K 3).torusSplit
      (GLn.groupData K 3).split_surjective (GLn.groupData K 3).split_eq_zero g).mp hg
    let t' : WithConv
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin 3) →₀ ℤ)) →ₐ[K] K) := t
    change pointsMulEquiv (R := K) (A := K) 3
      (TauCeti.AlgHom.mapDomain (GLn.torusRestriction K 3) t') ∈
        TauCeti.diagonalTorus K 3
    have he := MapPointsFunctor.diagonal_torus_app (R := K) (N := 3)
      (CommAlgCat.of K K) t'
    change TauCeti.AlgHom.mapDomain (GLn.torusRestriction K 3) t' =
      ReductiveGroups.diagonalTorusPoints t' at he
    rw [he, ReductiveGroups.pointsMulEquiv_diagonalTorusPoints
      (R := K) (N := 3) (A := K) t']
    apply TauCeti.mem_diagonalTorus_iff.mpr
    intro i j hij
    simp only [ReductiveGroups.diagGL_apply, ite_eq_right hij]
  · intro hg
    have hd := TauCeti.mem_diagonalTorus_iff.mp hg
    have hm := GLn.diagonal_mem_matrixPoints_torusIdeal
      (pointsMulEquiv (R := K) (A := K) 3 g)
      (fun i => (pointsMulEquiv (R := K) (A := K) 3 g : Matrix (Fin 3) (Fin 3) K) i i)
      hd.diagonal_diag.symm
    exact (GLn.groupData K 3).mem_torusPoints g |>.mpr
      ((pointsMulEquiv_mem_matrixPoints_iff (torusIdeal K 3) g).mp hm)

omit [CharZero K] in
private theorem map_torus :
    (GLn.groupData K 3).torusPoints.map (pointsMulEquiv (R := K) (A := K) 3).toMonoidHom =
      TauCeti.diagonalTorus K 3 := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (torus_matrix_iff g).mp hg
  · intro hm
    refine ⟨(pointsMulEquiv (R := K) (A := K) 3).symm m, ?_, MulEquiv.apply_symm_apply _ _⟩
    apply (torus_matrix_iff _).mpr
    simpa only [MulEquiv.apply_symm_apply] using hm

private def normalizerMatrices :
    (GLn.groupData K 3).torusNormalizer →*
      Subgroup.normalizer (TauCeti.diagonalTorus K 3 : Set (GL (Fin 3) K)) where
  toFun g := ⟨pointsMulEquiv (R := K) (A := K) 3 g.val, by
    have h := (GLn.groupData K 3).torusPoints.le_normalizer_map
      (pointsMulEquiv (R := K) (A := K) 3).toMonoidHom
      (show pointsMulEquiv (R := K) (A := K) 3 g.val ∈
        (GLn.groupData K 3).torusNormalizer.map
          (pointsMulEquiv (R := K) (A := K) 3).toMonoidHom from
          ⟨g.val, g.property, rfl⟩)
    have hN := congrArg
      (fun S : Subgroup (GL (Fin 3) K) => Subgroup.normalizer (S : Set (GL (Fin 3) K)))
      (map_torus (K := K))
    exact hN ▸ h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

private def normalizerPerm :
    (GLn.groupData K 3).torusNormalizer →* Equiv.Perm (Fin 3) :=
  TauCeti.diagonalNormalizerPerm.comp (normalizerMatrices (K := K))

private theorem normalizerPerm_eq_one (g : (GLn.groupData K 3).torusNormalizer) :
    normalizerPerm (K := K) g = 1 ↔ g.val ∈ (GLn.groupData K 3).torusPoints := by
  exact (TauCeti.diagonalNormalizerPerm_eq_one_iff (normalizerMatrices (K := K) g)).trans
    (torus_matrix_iff g.val).symm

private def weylPerm : (GLn.groupData K 3).weylGroup →* Equiv.Perm (Fin 3) :=
  (TauCeti.Subgroup.normalizerQuotientLift (GLn.groupData K 3).torusPoints
    (normalizerPerm (K := K)) (fun g hg => (normalizerPerm_eq_one g).mpr hg)).comp
      (GLn.groupData K 3).weylQuotientMap

private theorem weylPerm_injective : Function.Injective (weylPerm (K := K)) := by
  have hl := (TauCeti.Subgroup.normalizerQuotientLift_injective_iff
    (GLn.groupData K 3).torusPoints (normalizerPerm (K := K))
    (fun g hg => (normalizerPerm_eq_one g).mpr hg)).mpr normalizerPerm_eq_one
  exact hl.comp (GLn.groupData K 3).weylQuotientMap_injective

private theorem matrixRoot_neg (i j : Fin 3) (hij : i ≠ j) :
    -(matrixRoot (K := K) 3 i j hij) = matrixRoot 3 j i hij.symm := by
  have hs := matrixRoot_swap (K := K) i j hij
  have hn : (GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 i j hij)
      (matrixRoot 3 i j hij) = -(matrixRoot 3 i j hij) := by
    apply (GLn.groupData K 3).rootSystem.root.injective
    rw [(GLn.groupData K 3).rootSystem.root_reflectionPerm,
      (GLn.groupData K 3).rootSystem.reflection_apply_self]
    rfl
  exact hn.symm.trans hs

private theorem reflection_matrix_coefficients
    (i : (GLn.groupData K 3).rootBase.support) (a b : Fin 3) (hab : a ≠ b)
    (hi : i.val = matrixRoot 3 a b hab) :
    ∃ c d : K, c ≠ 0 ∧ d ≠ 0 ∧
      (pointsMulEquiv (R := K) (A := K) 3
        ((GLn.groupData K 3).reflectionPoint i.val) : Matrix (Fin 3) (Fin 3) K) =
        (1 + c • Matrix.single a b 1) *
          (1 - d • Matrix.single b a 1) * (1 + c • Matrix.single a b 1) := by
  let G := GLn.groupData K 3
  obtain ⟨c, hc, hcM⟩ := rootMap_matrix (K := K) 3 a b hab (G.simpleRootMap i)
    (by rw [← hi]; exact G.simpleRootMap_tangent_mem i)
    (G.simpleRootMap_tangent_ne_zero i)
  have hneg : -i.val = matrixRoot 3 b a hab.symm := by
    rw [hi]
    exact matrixRoot_neg a b hab
  obtain ⟨d, hd, hdM⟩ := rootMap_matrix (K := K) 3 b a hab.symm
    (G.negativeSimpleRootMap i)
    (by rw [← hneg]; exact G.negativeRootMap_tangent_mem i)
    (G.negativeRootMap_tangent_ne_zero i)
  refine ⟨c, d, hc, hd, ?_⟩
  have hr : G.reflectionPoint i.val =
      gaParameterPoint (G.simpleRootMap i) (1 : K) *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1 : K) *
          gaParameterPoint (G.simpleRootMap i) (1 : K) := rfl
  let e : G.points ≃* GL (Fin 3) K := pointsMulEquiv (R := K) (A := K) 3
  have hx (t : K) : (e (gaParameterPoint (G.simpleRootMap i) t) :
      Matrix (Fin 3) (Fin 3) K) = 1 + (t * c) • Matrix.single a b 1 := hcM t
  have hy (t : K) : (e (gaParameterPoint (G.negativeSimpleRootMap i) t) :
      Matrix (Fin 3) (Fin 3) K) = 1 + (t * d) • Matrix.single b a 1 := hdM t
  change (e (G.reflectionPoint i.val) : Matrix (Fin 3) (Fin 3) K) = _
  rw [hr]
  simp only [map_mul, Units.val_mul]
  rw [hx, hy]
  simp only [one_mul, neg_one_mul, neg_smul, sub_eq_add_neg]

private theorem reflection01_entries :
    ∃ d : K, d ≠ 0 ∧
      (pointsMulEquiv (R := K) (A := K) 3
        ((GLn.groupData K 3).reflectionPoint root01) : Matrix (Fin 3) (Fin 3) K) 1 0 =
          -d ∧
      (pointsMulEquiv (R := K) (A := K) 3
        ((GLn.groupData K 3).reflectionPoint root01) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  obtain ⟨c, d, _, hd, he⟩ := reflection_matrix_coefficients (K := K) simple01 0 1
    (by decide) rfl
  refine ⟨d, hd, ?_, ?_⟩
  · exact (congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 0) he).trans (by
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply])
  · exact (congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) he).trans (by
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply])

private theorem reflection12_entries :
    ∃ d : K, d ≠ 0 ∧
      (pointsMulEquiv (R := K) (A := K) 3
        ((GLn.groupData K 3).reflectionPoint root12) : Matrix (Fin 3) (Fin 3) K) 2 1 =
          -d ∧
      (pointsMulEquiv (R := K) (A := K) 3
        ((GLn.groupData K 3).reflectionPoint root12) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  obtain ⟨c, d, _, hd, he⟩ := reflection_matrix_coefficients (K := K) simple12 1 2
    (by decide) rfl
  refine ⟨d, hd, ?_, ?_⟩
  · exact (congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 1) he).trans (by
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply])
  · exact (congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) he).trans (by
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply])


private theorem perm_of_entry
    (g : (GLn.groupData K 3).torusNormalizer) (i j : Fin 3)
    (h : (pointsMulEquiv (R := K) (A := K) 3 g.val :
      Matrix (Fin 3) (Fin 3) K) i j ≠ 0) :
    normalizerPerm g j = i := by
  let m := normalizerMatrices (K := K) g
  obtain ⟨d, σ, he⟩ := TauCeti.mem_normalizer_diagonalTorus_iff_exists.mp m.property
  have hσ := TauCeti.diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL m d σ he
  change TauCeti.diagonalNormalizerPerm m j = i
  rw [hσ]
  by_contra hji
  apply h
  change ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0
  rw [he, TauCeti.coe_mul_permutationGL_apply, TauCeti.diagGL_coe,
    Matrix.diagonal_apply_ne _ (Ne.symm hji)]

private theorem reflection01_perm :
    normalizerPerm (K := K)
      ⟨(GLn.groupData K 3).reflectionPoint root01,
        (GLn.groupData K 3).isBruhatSystem.weyl.mem_normalizer root01⟩ =
      Equiv.swap (0 : Fin 3) 1 := by
  let n : (GLn.groupData K 3).torusNormalizer :=
    ⟨(GLn.groupData K 3).reflectionPoint root01,
      (GLn.groupData K 3).isBruhatSystem.weyl.mem_normalizer root01⟩
  let σ := normalizerPerm (K := K) n
  obtain ⟨d, hd, h10, h22⟩ := reflection01_entries (K := K)
  have h0 : σ 0 = 1 := perm_of_entry n 1 0
    (fun hz => (neg_ne_zero.mpr hd) (h10.symm.trans hz))
  have h2 : σ 2 = 2 := perm_of_entry n 2 2
    (fun hz => one_ne_zero (h22.symm.trans hz))
  have h1 : σ 1 = 0 := by
    have ha := σ.injective.ne (by decide : (1 : Fin 3) ≠ 0)
    have hb := σ.injective.ne (by decide : (1 : Fin 3) ≠ 2)
    rw [h0] at ha
    rw [h2] at hb
    omega
  change σ = _
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h0.trans (Equiv.swap_apply_left (0 : Fin 3) 1).symm
  · exact h1.trans (Equiv.swap_apply_right (0 : Fin 3) 1).symm
  · exact h2.trans (Equiv.swap_apply_of_ne_of_ne
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)).symm

private theorem reflection12_perm :
    normalizerPerm (K := K)
      ⟨(GLn.groupData K 3).reflectionPoint root12,
        (GLn.groupData K 3).isBruhatSystem.weyl.mem_normalizer root12⟩ =
      Equiv.swap (1 : Fin 3) 2 := by
  let n : (GLn.groupData K 3).torusNormalizer :=
    ⟨(GLn.groupData K 3).reflectionPoint root12,
      (GLn.groupData K 3).isBruhatSystem.weyl.mem_normalizer root12⟩
  let σ := normalizerPerm (K := K) n
  obtain ⟨d, hd, h21, h00⟩ := reflection12_entries (K := K)
  have h1 : σ 1 = 2 := perm_of_entry n 2 1
    (fun hz => (neg_ne_zero.mpr hd) (h21.symm.trans hz))
  have h0 : σ 0 = 0 := perm_of_entry n 0 0
    (fun hz => one_ne_zero (h00.symm.trans hz))
  have h2 : σ 2 = 1 := by
    have ha := σ.injective.ne (by decide : (2 : Fin 3) ≠ 0)
    have hb := σ.injective.ne (by decide : (2 : Fin 3) ≠ 1)
    rw [h0] at ha
    rw [h1] at hb
    omega
  change σ = _
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h0.trans (Equiv.swap_apply_of_ne_of_ne
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)).symm
  · exact h1.trans (Equiv.swap_apply_left (1 : Fin 3) 2).symm
  · exact h2.trans (Equiv.swap_apply_right (1 : Fin 3) 2).symm

private theorem weylPerm_simple (i : (GLn.groupData K 3).rootBase.support) :
    weylPerm (K := K) (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem i.val) =
      normalizerPerm (K := K)
        ⟨(GLn.groupData K 3).reflectionPoint i.val,
          (GLn.groupData K 3).isBruhatSystem.weyl.mem_normalizer i.val⟩ := by
  let G := GLn.groupData K 3
  let w := RootPairing.weylGroup.ofIdx G.rootSystem i.val
  let n : G.torusNormalizer := ⟨G.reflectionPoint i.val,
    G.isBruhatSystem.weyl.mem_normalizer i.val⟩
  let p : G.torusNormalizer := ⟨G.weylPoint w, G.weylPoint_mem_normalizer w⟩
  obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.simple_eq_mul_weylElementPoint G.rootBase i
  let z : G.torusNormalizer := ⟨t, G.torusPoints.le_normalizer ht⟩
  have hn : n = z * p := by
    apply Subtype.ext
    change G.reflectionPoint i.val = t * G.weylPoint w
    rw [G.weylPoint_eq]
    exact he
  have hz : normalizerPerm (K := K) z = 1 := (normalizerPerm_eq_one z).mpr ht
  change normalizerPerm (K := K) p = normalizerPerm (K := K) n
  rw [hn, map_mul, hz, one_mul]

private theorem weylPerm01 :
    weylPerm (K := K) (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem root01) =
      Equiv.swap (0 : Fin 3) 1 :=
  (weylPerm_simple simple01).trans reflection01_perm

private theorem weylPerm12 :
    weylPerm (K := K) (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem root12) =
      Equiv.swap (1 : Fin 3) 2 :=
  (weylPerm_simple simple12).trans reflection12_perm

private theorem weylPerm_word :
    weylPerm (K := K) (simpleWeylWord (GLn.groupData K 3).rootBase matrixWord) =
      Equiv.swap (0 : Fin 3) 2 := by
  calc
    _ = Equiv.swap (0 : Fin 3) 1 * (Equiv.swap 1 2 * Equiv.swap 0 1) := by
      simp only [matrixWord, simpleWeylWord, mul_one, map_mul, simple01, simple12,
        weylPerm01, weylPerm12]
    _ = _ := by decide

private theorem weylPerm_surjective : Function.Surjective (weylPerm (K := K)) := by
  let R := (weylPerm (K := K)).range
  have h01 : Equiv.swap (0 : Fin 3) 1 ∈ R := ⟨_, weylPerm01⟩
  have h12 : Equiv.swap (1 : Fin 3) 2 ∈ R := ⟨_, weylPerm12⟩
  have h02 : Equiv.swap (0 : Fin 3) 2 ∈ R := ⟨_, weylPerm_word⟩
  have hs (i j : Fin 3) : Equiv.swap i j ∈ R := by
    fin_cases i <;> fin_cases j
    · rw [Equiv.swap_self]
      change (1 : Equiv.Perm (Fin 3)) ∈ R
      exact R.one_mem
    · exact h01
    · exact h02
    · rw [Equiv.swap_comm]
      exact h01
    · rw [Equiv.swap_self]
      change (1 : Equiv.Perm (Fin 3)) ∈ R
      exact R.one_mem
    · exact h12
    · rw [Equiv.swap_comm]
      exact h02
    · rw [Equiv.swap_comm]
      exact h12
    · rw [Equiv.swap_self]
      change (1 : Equiv.Perm (Fin 3)) ∈ R
      exact R.one_mem
  intro σ
  exact σ.swap_induction_on R.one_mem (fun τ i j _ hτ => R.mul_mem (hs i j) hτ)

private theorem matrixWord_longest :
    simpleWeylWord (GLn.groupData K 3).rootBase matrixWord =
      (GLn.groupData K 3).longestElement := by
  let G := GLn.groupData K 3
  have hp (r : G.rootIndex) (hr : G.rootBase.IsPos r) :
      r = root01 ∨ r = root12 ∨ r = root02 := by
    obtain ⟨i, j, hij, hc⟩ := rootCharacter_pair 3 r
    have he : r = matrixRoot 3 i j hij := by
      apply G.characterRootEquiv.symm.injective
      apply Subtype.ext
      exact hc.trans (rootCharacter_matrixRoot 3 i j hij).symm
    subst r
    have hlt := (matrixRoot_positive 3 i j hij).mp hr
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 2) by omega) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hpos : {r | G.rootBase.IsPos r} ⊆ {root01, root12, root02} := by
    intro r hr
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp r hr
  have hpc : {r | G.rootBase.IsPos r}.ncard ≤ 3 := by
    have h := Set.ncard_le_ncard hpos
    have h1 := Set.ncard_insert_le (root01 (K := K)) {root12, root02}
    have h2 := Set.ncard_insert_le (root12 (K := K)) {root02}
    simp only [Set.ncard_singleton] at h2
    omega
  have hc : rootInversionCount G.rootBase (simpleWeylWord G.rootBase matrixWord) = 3 := by
    simpa only [matrixWord, List.length_cons, List.length_nil] using
      (weylCoxeterSystem_isReduced_iff G.rootBase matrixWord).mp matrixWord_reduced
  apply eq_longest_of_max G.rootBase
  intro w
  have hle := (rootInversionCount_le_longest G.rootBase w).trans_eq
    (rootInversionCount_longest G.rootBase)
  change rootInversionCount G.rootBase w ≤
    rootInversionCount G.rootBase (simpleWeylWord G.rootBase matrixWord)
  rw [hc]
  exact hle.trans hpc

/-- The two adjacent simple reflections identify the rank-three word with `321`. -/
theorem matrixWord_permutation :
    ∃ e : (GLn.groupData K 3).weylGroup ≃* Equiv.Perm (Fin 3),
      e (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem root01) =
        Equiv.swap 0 1 ∧
      e (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem root12) =
        Equiv.swap 1 2 ∧
      e (simpleWeylWord (GLn.groupData K 3).rootBase matrixWord) = Equiv.swap 0 2 ∧
      (∀ i : Fin 3, e (simpleWeylWord (GLn.groupData K 3).rootBase matrixWord) i =
        (![2, 1, 0] : Fin 3 → Fin 3) i) ∧
      (∀ i : Fin 3, e 1 i = (![0, 1, 2] : Fin 3 → Fin 3) i) ∧
      simpleWeylWord (GLn.groupData K 3).rootBase matrixWord =
        (GLn.groupData K 3).longestElement := by
  let e := MulEquiv.ofBijective (weylPerm (K := K))
    ⟨weylPerm_injective, weylPerm_surjective⟩
  refine ⟨e, weylPerm01, weylPerm12, weylPerm_word, ?_, ?_, matrixWord_longest⟩
  · intro i
    change weylPerm (K := K) (simpleWeylWord (GLn.groupData K 3).rootBase matrixWord) i = _
    rw [weylPerm_word]
    fin_cases i <;> decide
  · intro i
    rw [map_one]
    fin_cases i <;> rfl

end SchubertOrbits.GL3
