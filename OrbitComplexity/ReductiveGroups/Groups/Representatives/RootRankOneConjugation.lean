import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneReflection
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootReflectionConjugation
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Root Rank One Conjugation

Conjugating rank-one reflection points by torus normalizers.

Let `g` be a `K`-point of the original reductive group with
`g T(K) g⁻¹ ⊆ T(K)` for the fixed maximal torus `T`, and suppose that `Ad(g)`
maps the `α` character space into the `β` character space. For
`sl₂`-normalized pairs `(x_α, y_α)` and `(x_β, y_β)` we prove
`g n_α g⁻¹ = n_β(c)` for some `c ≠ 0`, hence `g n_α g⁻¹ ∈ T(K) · n_β`.

The steps are: `T(K)`-normalization gives `g`-stability of the torus ideal (by
point separation on the reduced torus coordinate ring), hence `Ad(g)` maps the
torus tangent image onto itself (finite dimension); then `dβ ∘ Ad(g) = dα` on
it, so `Ad(g)` maps the `α⁻¹` space into the `β⁻¹` space. One-dimensionality
gives `Ad(g) dx_α = c dx_β`, `Ad(g) dy_α = c' dy_β`, and the `sl₂` relations
force `c c' = 1`. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u

/-- A Lie automorphism carrying the root vectors of one `sl₂` triple to scalar
multiples `a e'`, `b f'` of the root vectors of another `sl₂` triple forces
`a * b = 1` (in characteristic zero). -/
theorem sl2_lieEquiv_scalars_mul_eq_one {K L : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] (φ : L ≃ₗ⁅K⁆ L)
    {h e f h' e' f' : L} (hs : IsSl2Triple h e f) (hs' : IsSl2Triple h' e' f')
    {a b : K} (ha : φ e = a • e') (hb : φ f = b • f') : a * b = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hs.e_ne_zero (φ.injective (ha.trans (map_zero φ).symm))
  have hh : φ h = (a * b) • h' := by
    rw [← hs.lie_e_f, LieEquiv.map_lie, ha, hb, smul_lie, lie_smul, hs'.lie_e_f, smul_smul]
  have he := congrArg φ (hs.lie_h_e_smul K)
  rw [LieEquiv.map_lie, hh, ha, map_smul, ha, smul_lie, lie_smul, hs'.lie_h_e_smul K,
    smul_smul, smul_smul, smul_smul] at he
  have hcoef := smul_left_injective K hs'.e_ne_zero he
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have : a * (a * b) * 2 = a * 2 := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcoef
  have h' := mul_right_cancel₀ h2 this
  calc a * b = a⁻¹ * (a * (a * b)) := by field_simp
    _ = 1 := by rw [h', inv_mul_cancel₀ ha0]

variable {K B ι : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

omit [CommRing B] [HopfAlgebra K B] in
/-- The coordinate ring of a finite-rank split torus is of finite type. -/
private theorem splitTorus_coordinate_finiteType' [Finite ι] :
    Algebra.FiniteType K (MonoidAlgebra K M) := by
  have hfg : Monoid.FG M :=
    Group.fg_iff_monoid_fg.mp (AddGroup.fg_iff_mul_fg.mp
      (Module.Finite.iff_addGroup_fg.mp inferInstance))
  exact @MonoidAlgebra.finiteType_of_fg K M _ _ hfg

/-- If `g T(K) g⁻¹ ⊆ T(K)` then conjugation by `g` maps the torus ideal into
itself. Over an algebraically closed field the `K`-points of the reduced
finite-type torus separate its coordinate functions. -/
theorem TorusIdeal.conjugation_mem_of_torusPoints_conj_mem
    [IsAlgClosed K] [Finite ι]
    (I : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K))
    (hg : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      g * t * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K))
    (a : B) (ha : a ∈ I) : affineGroupConjugationBialgHom g a ∈ I := by
  let _ : Algebra.FiniteType K (MonoidAlgebra K M) :=
    splitTorus_coordinate_finiteType' (K := K) (ι := ι)
  apply (hker _).mp
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (A := MonoidAlgebra K M) (K := K)
  intro τ
  rw [map_zero]
  let D : WithConv (B →ₐ[K] K) := TauCeti.AlgHom.mapDomain π (WithConv.toConv τ)
  have hD := hg D (mapDomain_mem_torusPoints I π hπ hker _)
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hD
  have hDa := hD a ha
  have hpt := affineGroupConjugationAlgHom_point g D
  have hs : WithConv.toConv ((IsScalarTower.toAlgHom K K K).comp g.ofConv) = g := by
    apply WithConv.ofConv_injective
    ext b
    rfl
  rw [hs] at hpt
  rw [← hpt] at hDa
  exact hDa

variable [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι]

omit [CharZero K] in
/-- If `g T(K) g⁻¹ ⊆ T(K)` then `Ad(g)` maps the torus tangent image into
itself and onto itself. -/
theorem RootRankOneConjugation.torusTangent_of_torusPoints_conj_mem
    (I : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K))
    (hg : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      g * t * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K)) :
    (∀ t : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g (t : 𝔤) ∈ diagonalizableTangentImage π) ∧
    (∀ t : diagonalizableTangentImage π, ∃ u : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤)) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let H := diagonalizableTangentImage π
  have hAd : ∀ t : H, affineGroupAdjointRepresentation g (t : 𝔤) ∈ H := by
    intro t
    have hcomp : affineGroupAdjointRepresentation g (t : 𝔤) =
        TauCeti.derivationComp (B := K) (affineGroupConjugationBialgHom g) (t : 𝔤) := by
      rw [DerivationComp.conjugation, affineGroupAdjointRepresentation_apply]
    rw [hcomp]
    apply (tangent_mem_range_iff_kills_kernel π hπ _).mpr
    intro a ha
    rw [TauCeti.derivationComp_apply]
    apply (tangent_mem_range_iff_kills_kernel π hπ (t : 𝔤)).mp t.property
    exact (hker _).mpr (TorusIdeal.conjugation_mem_of_torusPoints_conj_mem I π hπ hker g hg a
      ((hker a).mp ha))
  refine ⟨hAd, ?_⟩
  let f : 𝔤 →ₗ[K] 𝔤 := affineGroupAdjointRepresentation g
  have hmaps : ∀ v ∈ H.toSubmodule, f v ∈ H.toSubmodule := fun v hv => hAd ⟨v, hv⟩
  have hinj : Set.InjOn f H.toSubmodule :=
    (affineGroupAdjointLieEquiv g).injective.injOn
  have hsurj := (LinearMap.injOn_iff_surjOn hmaps).mp hinj
  intro t
  obtain ⟨u, hu, hfu⟩ := hsurj t.property
  exact ⟨⟨u, hu⟩, hfu⟩

omit [IsAlgClosed K] [CharZero K] [Finite ι] in
/-- If `Ad(g)` maps the torus tangent image into itself and maps a nonzero
vector of the `α` character space into the `β` character space, then
`dβ(Ad(g) t) = dα(t)` on the torus tangent image. -/
theorem CharacterDifferential.adjoint_of_weight_transport
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ t : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g (t : 𝔤) ∈ diagonalizableTangentImage π)
    (α β : M) (d : 𝔤) (hd : d ∈ affineGroupCharacterWeightSpace π α) (hd0 : d ≠ 0)
    (hgd : affineGroupAdjointRepresentation g d ∈ affineGroupCharacterWeightSpace π β)
    (t : diagonalizableTangentImage π) :
    characterDifferentialOnImage π hπ β ⟨_, hAd t⟩ = characterDifferentialOnImage π hπ α t := by
  have h1 := RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ β _ hgd ⟨_, hAd t⟩
  have h2 := (affineGroupAdjointLieEquiv g).map_lie (t : 𝔤) d
  change affineGroupAdjointRepresentation g ⁅(t : 𝔤), d⁆ =
    ⁅affineGroupAdjointRepresentation g (t : 𝔤), affineGroupAdjointRepresentation g d⁆ at h2
  rw [RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ α d hd t, map_smul] at h2
  change ⁅affineGroupAdjointRepresentation g (t : 𝔤), affineGroupAdjointRepresentation g d⁆ =
    _ at h1
  rw [← h2] at h1
  have hne : affineGroupAdjointRepresentation g d ≠ 0 := by
    intro hz
    apply hd0
    exact (affineGroupAdjointLieEquiv g).injective (hz.trans (map_zero _).symm)
  exact smul_left_injective K hne h1.symm

/-- **Conjugating reflection points.** In the original reductive group, let `g`
satisfy `g T(K) g⁻¹ ⊆ T(K)` and let `Ad(g)` map the `α` character space into the
`β` character space. For `sl₂`-normalized pairs `(x_α, y_α)` for `α` and
`(x_β, y_β)` for `β`, there is `c ≠ 0` with
`g · x_α(1) y_α(-1) x_α(1) · g⁻¹ = x_β(c) y_β(-c⁻¹) x_β(c)`. -/
theorem RootRankOneConjugation.eq_rootReflectionPointAt
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (g : WithConv (B →ₐ[K] K))
    (hg : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      g * t * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K))
    {α β : M} {xα yα xβ yβ : B →ₐc[K] SymmetricAlgebra K K}
    (hpα : IsRootSl2Pair π α xα yα) (hpβ : IsRootSl2Pair π β xβ yβ)
    (hαβ : ∀ d ∈ affineGroupCharacterWeightSpace π α,
      affineGroupAdjointRepresentation g d ∈ affineGroupCharacterWeightSpace π β) :
    ∃ c : K, c ≠ 0 ∧
      g * rootReflectionPoint xα yα * g⁻¹ = rootReflectionPointAt xβ yβ c := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let H := diagonalizableTangentImage π
  obtain ⟨hAd, honto⟩ := RootRankOneConjugation.torusTangent_of_torusPoints_conj_mem I π hπ hker g
    hg
  have hxα := hpα.tangent_mem
  have hgx : affineGroupAdjointRepresentation g (gaAffineGroupTangent xα) ∈
      affineGroupCharacterWeightSpace π β := hαβ _ hxα
  have hχ := CharacterDifferential.adjoint_of_weight_transport π hπ g hAd α β _ hxα
    hpα.tangent_ne_zero hgx
  -- `Ad(g)` carries the `α⁻¹` space into the `β⁻¹` space.
  have hgy : affineGroupAdjointRepresentation g (gaAffineGroupTangent yα) ∈
      affineGroupCharacterWeightSpace π β⁻¹ := by
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ β⁻¹]
    apply AffineGroupAdjoint.mem_rootSpace_of_eigen_transport H g
      (characterDifferentialOnImage π hπ α⁻¹) (characterDifferentialOnImage π hπ β⁻¹)
      hAd honto
    · intro t
      rw [characterDifferentialOnImage_inv, characterDifferentialOnImage_inv,
        LinearMap.neg_apply, LinearMap.neg_apply, hχ t]
    · exact RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ α⁻¹ _
        hpα.partner_tangent_mem
  -- One-dimensionality of the `β` and `β⁻¹` spaces.
  have hβ1 := hpβ.ne_one hπ
  have hfinβ := ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB β hβ1
    hpβ.characterWeightSpace_ne_bot
  have hfinβinv := ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB β⁻¹
    (inv_ne_one.mpr hβ1) hpβ.partner_characterWeightSpace_ne_bot
  have hxβ0 : (⟨gaAffineGroupTangent xβ, hpβ.tangent_mem⟩ :
      affineGroupCharacterWeightSpace π β) ≠ 0 := by
    intro hz
    exact hpβ.tangent_ne_zero (congrArg Subtype.val hz)
  have hyβ0 : (⟨gaAffineGroupTangent yβ, hpβ.partner_tangent_mem⟩ :
      affineGroupCharacterWeightSpace π β⁻¹) ≠ 0 := by
    intro hz
    exact hpβ.partner_tangent_ne_zero (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hxβ0).mp hfinβ ⟨_, hgx⟩
  obtain ⟨c', hc'⟩ := (finrank_eq_one_iff_of_nonzero' _ hyβ0).mp hfinβinv ⟨_, hgy⟩
  have hcx : affineGroupAdjointRepresentation g (gaAffineGroupTangent xα) =
      c • gaAffineGroupTangent xβ := (congrArg Subtype.val hc).symm
  have hcy : affineGroupAdjointRepresentation g (gaAffineGroupTangent yα) =
      c' • gaAffineGroupTangent yβ := (congrArg Subtype.val hc').symm
  have hcc : c * c' = 1 :=
    sl2_lieEquiv_scalars_mul_eq_one (affineGroupAdjointLieEquiv g)
      hpα.isSl2Triple hpβ.isSl2Triple hcx hcy
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hc'eq : c' = c⁻¹ := eq_inv_of_mul_eq_one_right hcc
  refine ⟨c, hc0, ?_⟩
  have hX (u : K) := GaAffineGroupPoints.conjugate_of_tangent_eq xα xβ g c hcx u
  have hY (u : K) := GaAffineGroupPoints.conjugate_of_tangent_eq yα yβ g c' hcy u
  have hsplit : g * rootReflectionPoint xα yα * g⁻¹ =
      (g * gaAffineGroupPoints xα (Multiplicative.ofAdd (1 : K)) * g⁻¹) *
        (g * gaAffineGroupPoints yα (Multiplicative.ofAdd (-1 : K)) * g⁻¹) *
          (g * gaAffineGroupPoints xα (Multiplicative.ofAdd (1 : K)) * g⁻¹) := by
    rw [rootReflectionPoint]
    group
  rw [hsplit, hX, hY, mul_one, mul_neg_one, hc'eq, rootReflectionPointAt]

/-- **Conjugating reflection points into `T(K) · n_β`.** Under the hypotheses of
`ReductiveGroups.RootRankOneConjugation.eq_rootReflectionPointAt`,
`g n_α g⁻¹ = t n_β` for some `t ∈ T(K)`, where `n_γ = x_γ(1) y_γ(-1) x_γ(1)`. -/
theorem conj_rootReflectionPoint_mem_torus_mul
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (g : WithConv (B →ₐ[K] K))
    (hg : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      g * t * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K))
    {α β : M} {xα yα xβ yβ : B →ₐc[K] SymmetricAlgebra K K}
    (hpα : IsRootSl2Pair π α xα yα) (hpβ : IsRootSl2Pair π β xβ yβ)
    (hαβ : ∀ d ∈ affineGroupCharacterWeightSpace π α,
      affineGroupAdjointRepresentation g d ∈ affineGroupCharacterWeightSpace π β) :
    ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      g * rootReflectionPoint xα yα * g⁻¹ = t * rootReflectionPoint xβ yβ := by
  obtain ⟨c, hc0, hc⟩ := RootRankOneConjugation.eq_rootReflectionPointAt I hI π hπ hker hB
    g hg hpα hpβ hαβ
  rw [hc]
  exact hpβ.rootReflectionPointAt_mem_torus_mul I hπ hker hc0


/-- `conj_rootReflectionPoint_mem_torus_mul` for `g` in the normalizer of the
torus point subgroup `T(K)`. -/
theorem RootRankOneConjugation.mem_torus_mul_of_mem_normalizer
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (g : WithConv (B →ₐ[K] K))
    (hg : g ∈ Subgroup.normalizer
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K) : Set (WithConv (B →ₐ[K] K))))
    {α β : M} {xα yα xβ yβ : B →ₐc[K] SymmetricAlgebra K K}
    (hpα : IsRootSl2Pair π α xα yα) (hpβ : IsRootSl2Pair π β xβ yβ)
    (hαβ : ∀ d ∈ affineGroupCharacterWeightSpace π α,
      affineGroupAdjointRepresentation g d ∈ affineGroupCharacterWeightSpace π β) :
    ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      g * rootReflectionPoint xα yα * g⁻¹ = t * rootReflectionPoint xβ yβ :=
  conj_rootReflectionPoint_mem_torus_mul I hI π hπ hker hB g
    (fun t ht => (Subgroup.mem_normalizer_iff.mp hg t).mp ht) hpα hpβ hαβ

end ReductiveGroups
