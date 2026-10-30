import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootParameters
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSigns
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaClosedImmersion

/-! # Compatible additive root parameters and signed representative transport -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open LieAlgebra LieModule TauCeti

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem root_quotient_injective (r : G.rootIndex) {a b : G.tangent}
    (ha : a ∈ G.rootWeightSpace r) (hb : b ∈ G.rootWeightSpace r)
    (h : centerQuotientLieHom (K := K) a = centerQuotientLieHom (K := K) b) : a = b := by
  have he : G.rootWeightQuotientEquiv r ⟨a, ha⟩ =
      G.rootWeightQuotientEquiv r ⟨b, hb⟩ := by
    apply Subtype.ext
    simpa only [rootWeightQuotientEquiv_apply] using h
  exact congrArg Subtype.val ((G.rootWeightQuotientEquiv r).injective he)

private theorem parameter_unit_comparison
    (r : G.rootIndex) (φ ψ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hφ : gaAffineGroupTangent φ ∈ G.rootWeightSpace r)
    (hφn : gaAffineGroupTangent φ ≠ 0)
    (hψ : gaAffineGroupTangent ψ ∈ G.rootWeightSpace r)
    (hψn : gaAffineGroupTangent ψ ≠ 0) :
    ∃ c : Kˣ, ∀ a : K, gaParameterPoint ψ a = gaParameterPoint φ ((c : K) * a) := by
  have hn : (⟨gaAffineGroupTangent φ, hφ⟩ : G.rootWeightSpace r) ≠ 0 := by
    intro h
    exact hφn (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hn).mp
    (G.rootWeightSpace_finrank r)
    (⟨gaAffineGroupTangent ψ, hψ⟩ : G.rootWeightSpace r)
  have he : c • gaAffineGroupTangent φ = gaAffineGroupTangent ψ :=
    congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    intro hz
    apply hψn
    rw [← he, hz]
    exact zero_smul K (gaAffineGroupTangent φ)
  refine ⟨Units.mk0 c hc0, ?_⟩
  intro a
  have hlin : affineGroupAdjointRepresentation (1 : G.points) (gaAffineGroupTangent ψ) =
      c • gaAffineGroupTangent φ := by
    simpa only [map_one, Module.End.one_apply] using he.symm
  simpa only [gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, one_mul, inv_one, mul_one, Units.val_mk0] using
    GaAffineGroupPoints.conjugate_of_tangent_eq ψ φ (1 : G.points) c hlin a

private theorem conjugate_of_root_sign
    (x : Weight K G.cartan G.centerQuotient → G.centerQuotient)
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hm : ∀ r, gaAffineGroupTangent (φ r) ∈ G.rootWeightSpace r)
    (hq : ∀ r, centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r)) = x r.val)
    (p : G.points) (τ : Equiv.Perm G.rootIndex) (hp : G.rootPointTransport p τ)
    (r : G.rootIndex) (ε : K)
    (hε : centerQuotientEquiv (affineGroupAdjointLieEquiv p) (x r.val) =
      ε • x (τ r).val) (a : K) :
    p * gaParameterPoint (φ r) a * p⁻¹ = gaParameterPoint (φ (τ r)) (ε * a) := by
  have hmapped : affineGroupAdjointRepresentation p (gaAffineGroupTangent (φ r)) ∈
      G.rootWeightSpace (τ r) := by
    rw [← hp r]
    exact ⟨gaAffineGroupTangent (φ r), hm r, rfl⟩
  have he : centerQuotientLieHom (K := K)
      (affineGroupAdjointRepresentation p (gaAffineGroupTangent (φ r))) =
      centerQuotientLieHom (K := K) (ε • gaAffineGroupTangent (φ (τ r))) := by
    calc
      _ = centerQuotientEquiv (affineGroupAdjointLieEquiv p)
          (centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r))) := by
        rw [centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply]
      _ = ε • x (τ r).val := by rw [hq, hε]
      _ = _ := by rw [map_smul, hq]
  have hlin := root_quotient_injective G (τ r) hmapped
    ((G.rootWeightSpace (τ r)).smul_mem ε (hm (τ r))) he
  simpa only [gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] using
    GaAffineGroupPoints.conjugate_of_tangent_eq (φ r) (φ (τ r)) p ε hlin a

private theorem word_conjugate (f : G.rootIndex → G.points)
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hs : ∀ (i : G.rootBase.support) (r : G.rootIndex),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        f i.val * gaParameterPoint (φ r) a * (f i.val)⁻¹ =
          gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r)) (ε * a))
    (l : List G.rootBase.support) (r : G.rootIndex) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
      simpleWordPoint f G.rootBase l * gaParameterPoint (φ r) a *
          (simpleWordPoint f G.rootBase l)⁻¹ =
        gaParameterPoint (φ (G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l) r))
          (ε * a) := by
  induction l generalizing r with
  | nil =>
    refine ⟨1, Or.inl rfl, ?_⟩
    intro a
    simp only [simpleWordPoint_nil, simpleWeylWord, map_one, Equiv.Perm.one_apply,
      one_mul, inv_one, mul_one]
  | cons i l ih =>
    obtain ⟨ε, hε, he⟩ := ih r
    let r' := G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l) r
    obtain ⟨δ, hδ, hd⟩ := hs i r'
    refine ⟨δ * ε, ?_, ?_⟩
    · rcases hδ with rfl | rfl <;> rcases hε with rfl | rfl <;> simp
    · intro a
      have hr : G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase (i :: l)) r =
          G.rootSystem.reflectionPerm i.val r' := by
        simp only [simpleWeylWord, map_mul, weylGroupToPerm_simple, Equiv.Perm.mul_apply]
        rfl
      rw [simpleWordPoint_cons, hr]
      calc
        _ = f i.val *
            (simpleWordPoint f G.rootBase l * gaParameterPoint (φ r) a *
              (simpleWordPoint f G.rootBase l)⁻¹) *
            (f i.val)⁻¹ := by group
        _ = f i.val * gaParameterPoint (φ r') (ε * a) *
            (f i.val)⁻¹ := by rw [he]
        _ = gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r')) (δ * (ε * a)) :=
          hd (ε * a)
        _ = _ := by rw [mul_assoc]

private theorem inverse_simple_conjugate
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hs : ∀ (i : G.rootBase.support) (r : G.rootIndex),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        G.reflectionPoint i.val * gaParameterPoint (φ r) a * (G.reflectionPoint i.val)⁻¹ =
          gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r)) (ε * a))
    (i : G.rootBase.support) (r : G.rootIndex) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
      (G.reflectionPoint i.val)⁻¹ * gaParameterPoint (φ r) a *
          ((G.reflectionPoint i.val)⁻¹)⁻¹ =
        gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r)) (ε * a) := by
  obtain ⟨ε, hε, he⟩ := hs i (G.rootSystem.reflectionPerm i.val r)
  refine ⟨ε, hε, ?_⟩
  intro a
  have hεsq : ε * (ε * a) = a := by
    rcases hε with rfl | rfl <;> simp
  have he' : G.reflectionPoint i.val *
      gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r)) (ε * a) *
      (G.reflectionPoint i.val)⁻¹ = gaParameterPoint (φ r) a := by
    simpa only [RootPairing.reflectionPerm_self, hεsq] using he (ε * a)
  rw [inv_inv]
  calc
    _ = (G.reflectionPoint i.val)⁻¹ *
        (G.reflectionPoint i.val *
          gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r)) (ε * a) *
          (G.reflectionPoint i.val)⁻¹) * G.reflectionPoint i.val := by rw [he']
    _ = _ := by group

/-- Compatible root parameters have signed forward and inverse-word transport. -/
theorem exists_rootParameterFamily :
  ∃ (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
    (x : Weight K G.cartan G.centerQuotient → G.centerQuotient)
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K),
    IsChevalleySystem ω x ∧
    (∀ r, gaAffineGroupTangent (φ r) ∈ G.rootWeightSpace r ∧
      centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r)) = x r.val ∧
      Function.Surjective (φ r)) ∧
    (∀ i : G.rootBase.support,
      φ i.val = G.simpleRootMap i ∧ φ (-i.val) = G.negativeSimpleRootMap i) ∧
    (∀ (r : G.rootIndex) (ψ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K),
      gaAffineGroupTangent ψ ∈ G.rootWeightSpace r → gaAffineGroupTangent ψ ≠ 0 →
      ∃ c : Kˣ, ∀ a : K, gaParameterPoint ψ a = gaParameterPoint (φ r) ((c : K) * a)) ∧
    (∀ (w : G.weylGroup) (r : G.rootIndex),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        G.weylPoint w * gaParameterPoint (φ r) a * (G.weylPoint w)⁻¹ =
          gaParameterPoint (φ (G.rootSystem.weylGroupToPerm w r)) (ε * a)) ∧
    ∀ (l : List G.rootBase.support) (r : G.rootIndex),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase l *
            gaParameterPoint (φ r) a *
            (simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
              G.rootBase l)⁻¹ =
          gaParameterPoint
            (φ (G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l) r)) (ε * a) := by
  obtain ⟨ω, x, hx, hi, hs⟩ := G.exists_simpleRootSigns
  let d (r : G.rootIndex) : G.rootWeightSpace r :=
    (G.rootWeightQuotientEquiv r).symm ⟨x r.val, hx.toIsSl2System.mem_rootSpace r.val⟩
  let φ (r : G.rootIndex) : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
    (G.existsUnique_rootParameter r (d r) (d r).property).choose
  have hφ (r : G.rootIndex) : gaAffineGroupTangent (φ r) = (d r : G.tangent) :=
    (G.existsUnique_rootParameter r (d r) (d r).property).choose_spec.1
  have hm (r : G.rootIndex) : gaAffineGroupTangent (φ r) ∈ G.rootWeightSpace r := by
    rw [hφ]
    exact (d r).property
  have hq (r : G.rootIndex) :
      centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r)) = x r.val := by
    rw [hφ]
    exact (G.rootWeightQuotientEquiv_apply r (d r)).symm.trans
      (congrArg Subtype.val ((G.rootWeightQuotientEquiv r).apply_symm_apply
        ⟨x r.val, hx.toIsSl2System.mem_rootSpace r.val⟩))
  have hn (r : G.rootIndex) : gaAffineGroupTangent (φ r) ≠ 0 := by
    intro hz
    have he := hq r
    rw [hz, map_zero] at he
    exact hx.toIsSl2System.ne_zero r.val (LieSubalgebra.isNonZero_coe_root r) he.symm
  have hsimple : ∀ (i : G.rootBase.support) (r : G.rootIndex),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        G.reflectionPoint i.val * gaParameterPoint (φ r) a * (G.reflectionPoint i.val)⁻¹ =
          gaParameterPoint (φ (G.rootSystem.reflectionPerm i.val r)) (ε * a) := by
    intro i r
    rcases hs i r with hp | hn
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro a
      apply conjugate_of_root_sign G x φ hm hq (G.reflectionPoint i.val)
        (G.rootSystem.reflectionPerm i.val)
        (G.isBruhatSystem.weyl.transport_reflection i.val) r 1 _ a
      simpa only [one_smul] using hp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro a
      apply conjugate_of_root_sign G x φ hm hq (G.reflectionPoint i.val)
        (G.rootSystem.reflectionPerm i.val)
        (G.isBruhatSystem.weyl.transport_reflection i.val) r (-1) _ a
      simpa only [neg_one_smul] using hn
  refine ⟨ω, x, φ, hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ⟨hm r, hq r, gaMorphism_surjective_of_tangent_ne_zero (φ r) (hn r)⟩
  · intro i
    constructor
    · apply gaMorphism_ext_of_tangent_eq
      exact root_quotient_injective G i.val (hm i.val) (G.simpleRootMap_tangent_mem i)
        ((hq i.val).trans (hi i).1)
    · apply gaMorphism_ext_of_tangent_eq
      exact root_quotient_injective G (-i.val) (hm (-i.val))
        (G.negativeRootMap_tangent_mem i) ((hq (-i.val)).trans (hi i).2)
  · intro r ψ hψ hψn
    exact parameter_unit_comparison G r (φ r) ψ (hm r) (hn r) hψ hψn
  · intro w r
    rw [G.weylPoint_eq w]
    simpa only [weylElementPoint, simpleWeylWord_chosenReducedWord] using
      word_conjugate G G.reflectionPoint φ hsimple (chosenReducedWord G.rootBase w) r

  · intro l r
    exact word_conjugate G (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
      φ (inverse_simple_conjugate G φ hsimple) l r

end ReductiveGroups.ReductiveGroupData
