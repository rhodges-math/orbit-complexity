import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.RootParameterSigns

/-! # Common signs for opposite root parameters -/

noncomputable section
namespace ReductiveGroups

private theorem word_transport {ι R M N A : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Group A]
    {P : RootPairing ι R M N} (b : P.Base) (f : ι → A)
    (Tr : A → Equiv.Perm ι → Prop) (hone : Tr 1 1)
    (hmul : ∀ g h σ τ, Tr g σ → Tr h τ → Tr (g * h) (σ * τ))
    (hs : ∀ r, Tr (f r) (P.reflectionPerm r)) (l : List b.support) :
    Tr (simpleWordPoint f b l) (P.weylGroupToPerm (simpleWeylWord b l)) := by
  induction l with
  | nil =>
    rw [simpleWordPoint_nil, show simpleWeylWord b [] = 1 from rfl, map_one]
    exact hone
  | cons i l ih =>
    rw [simpleWordPoint_cons, show simpleWeylWord b (i :: l) =
      RootPairing.weylGroup.ofIdx P i.val * simpleWeylWord b l from rfl,
      map_mul, weylGroupToPerm_simple (P := P) i.val]
    exact hmul _ _ _ _ (hs i.val) ih

end ReductiveGroups

namespace ReductiveGroups.ReductiveGroupData
open LieAlgebra LieModule TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem weyl_neg (w : G.weylGroup) (r : G.rootIndex) :
    G.rootSystem.weylGroupToPerm w (-r) = -G.rootSystem.weylGroupToPerm w r := by
  apply G.rootSystem.root.injective
  rw [← G.rootSystem.weylGroup_apply_root]
  change w • (-G.rootSystem.root r) = -(G.rootSystem.root
    (G.rootSystem.weylGroupToPerm w r))
  rw [smul_neg, G.rootSystem.weylGroup_apply_root]

private theorem rootTransport_inv {g : G.points} {σ : Equiv.Perm G.rootIndex}
    (h : G.rootPointTransport g σ) : G.rootPointTransport g⁻¹ σ⁻¹ := by
  intro r
  have hcomp :
      ((affineGroupAdjointLieEquiv g⁻¹).toLinearEquiv.toLinearMap).comp
        ((affineGroupAdjointLieEquiv g).toLinearEquiv.toLinearMap) = LinearMap.id := by
    apply LinearMap.ext
    intro d
    change affineGroupAdjointRepresentation g⁻¹ (affineGroupAdjointRepresentation g d) = d
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv := congrArg (fun S : Submodule K G.tangent => S.map
    ((affineGroupAdjointLieEquiv g⁻¹).toLinearEquiv.toLinearMap)) (h (σ⁻¹ r))
  simp only [← Submodule.map_comp, hcomp, Submodule.map_id] at hinv
  simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hinv.symm

private theorem inverseReflection_transport (r : G.rootIndex) :
    G.rootPointTransport (G.reflectionPoint r)⁻¹ (G.rootSystem.reflectionPerm r) := by
  have hr : G.rootPointTransport (G.reflectionPoint r) (G.rootSystem.reflectionPerm r) :=
    G.isBruhatSystem.weyl.transport_reflection r
  have hinv : G.rootPointTransport (G.reflectionPoint r)⁻¹
      (G.rootSystem.reflectionPerm r)⁻¹ := rootTransport_inv G hr
  simpa only [RootPairing.reflectionPerm_inv] using hinv

private theorem inverse_word_transport (l : List G.rootBase.support) :
    G.rootPointTransport
      (simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase l)
      (G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l)) :=
  word_transport G.rootBase (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
    G.rootPointTransport G.isBruhatSystem.weyl.transport_one
    G.isBruhatSystem.weyl.transport_mul (inverseReflection_transport G) l

private theorem paired_conjugate
    (x : Weight K G.cartan G.centerQuotient → G.centerQuotient) (hx : IsSl2System x)
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hm : ∀ r, gaAffineGroupTangent (φ r) ∈ G.rootWeightSpace r)
    (hq : ∀ r, centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r)) = x r.val)
    (p : G.points) (τ : Equiv.Perm G.rootIndex) (hp : G.rootPointTransport p τ)
    (hneg : ∀ r, τ (-r) = -τ r)
    (hs : ∀ r, ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
      p * gaParameterPoint (φ r) a * p⁻¹ = gaParameterPoint (φ (τ r)) (ε * a))
    (r : G.rootIndex) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
      (p * gaParameterPoint (φ r) a * p⁻¹ = gaParameterPoint (φ (τ r)) (ε * a)) ∧
      (p * gaParameterPoint (φ (-r)) a * p⁻¹ = gaParameterPoint (φ (-τ r)) (ε * a)) := by
  obtain ⟨a, ha, he⟩ := hs r
  obtain ⟨b, _, hf⟩ := hs (-r)
  have hasq : a * a = 1 := by rcases ha with rfl | rfl <;> simp
  have hab := root_parameter_signs_equal G x hx φ hm hq p τ hp hneg r a b hasq he hf
  refine ⟨a, ha, fun t => ⟨he t, ?_⟩⟩
  simpa only [hneg, ← hab] using hf t

/-- Opposite root parameters share the sign of every forward or inverse-word transport. -/
theorem exists_pairedRootParameters :
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
        (G.weylPoint w * gaParameterPoint (φ r) a * (G.weylPoint w)⁻¹ =
          gaParameterPoint (φ (G.rootSystem.weylGroupToPerm w r)) (ε * a)) ∧
        (G.weylPoint w * gaParameterPoint (φ (-r)) a * (G.weylPoint w)⁻¹ =
          gaParameterPoint (φ (-G.rootSystem.weylGroupToPerm w r)) (ε * a))) ∧
    ∀ (l : List G.rootBase.support) (r : G.rootIndex),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        (simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase l *
            gaParameterPoint (φ r) a *
            (simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
              G.rootBase l)⁻¹ =
          gaParameterPoint
            (φ (G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l) r)) (ε * a)) ∧
        (simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase l *
            gaParameterPoint (φ (-r)) a *
            (simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
              G.rootBase l)⁻¹ =
          gaParameterPoint
            (φ (-G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l) r)) (ε * a)) :=
  Exists.elim (G.exists_rootParameterFamily) fun ω hω =>
    Exists.elim hω fun x hx' =>
      Exists.elim hx' fun φ hφ =>
        ⟨ω, x, φ, hφ.1, hφ.2.1, hφ.2.2.1, hφ.2.2.2.1,
          fun w r => paired_conjugate G x hφ.1.toIsSl2System φ
            (fun s => (hφ.2.1 s).1) (fun s => (hφ.2.1 s).2.1)
            (G.weylPoint w) (G.rootSystem.weylGroupToPerm w)
            (G.weylPoint_rootWeightSpace w) (weyl_neg G w) (hφ.2.2.2.2.1 w) r,
          fun l r => paired_conjugate G x hφ.1.toIsSl2System φ
            (fun s => (hφ.2.1 s).1) (fun s => (hφ.2.1 s).2.1)
            (simpleWordPoint (fun s : G.rootIndex => (G.reflectionPoint s)⁻¹) G.rootBase l)
            (G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase l))
            (inverse_word_transport G l) (weyl_neg G (simpleWeylWord G.rootBase l))
            (hφ.2.2.2.2.2 l) r⟩

end ReductiveGroups.ReductiveGroupData
