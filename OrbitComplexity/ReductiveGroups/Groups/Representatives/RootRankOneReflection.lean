import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneSl2Pair
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusAdjointNormalizer

/-!
# Root Rank One Reflection

Rank-one reflection points built from an `sl₂`-normalized pair.

For `Ga` morphisms `x, y` into the original group, set
`n(c) = x(c) y(-c⁻¹) x(c)` and `n = x(1) y(-1) x(1)`, as `K`-points of the
original group. When `(x, y)` is an `sl₂`-normalized pair for a torus character
`α`, the point `n`

* acts on the torus tangent image by `t ↦ t - dα(t) ⁅dx, dy⁆`;
* normalizes the `K`-points `T(K)` of the fixed torus
  (`g ∈ T(K) ↔ n g n⁻¹ ∈ T(K)`);
* satisfies `n(c) ∈ T(K) · n` for every `c ≠ 0` (rescaling by a torus point
  with `α`-value `c`, which exists over an algebraically closed field), so
  `n(c)` normalizes `T(K)` as well;
* has `n⁻¹ = n(-1) ∈ T(K) · n` and `n² ∈ T(K)`;
* gives the rank-one Bruhat relation `y(d) = x(d⁻¹) t n x(d⁻¹)`, `t ∈ T(K)`,
  for every `d ≠ 0`.

 -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The point `x(c) y(-c⁻¹) x(c)` of the original group. -/
def rootReflectionPointAt (x y : B →ₐc[K] SymmetricAlgebra K K) (c : K) :
    WithConv (B →ₐ[K] K) :=
  gaAffineGroupPoints x (Multiplicative.ofAdd c) *
    gaAffineGroupPoints y (Multiplicative.ofAdd (-c⁻¹)) *
      gaAffineGroupPoints x (Multiplicative.ofAdd c)

/-- The point `x(1) y(-1) x(1)` of the original group. -/
def rootReflectionPoint (x y : B →ₐc[K] SymmetricAlgebra K K) : WithConv (B →ₐ[K] K) :=
  gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
    gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
      gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))

/-- `n(1) = n`. -/
theorem rootReflectionPointAt_one (x y : B →ₐc[K] SymmetricAlgebra K K) :
    rootReflectionPointAt x y 1 = rootReflectionPoint x y := by
  rw [rootReflectionPointAt, rootReflectionPoint, inv_one]

/-- Inverses of additive-subgroup points: `x(c)⁻¹ = x(-c)`. -/
theorem gaAffineGroupPoints_ofAdd_inv (x : B →ₐc[K] SymmetricAlgebra K K) (c : K) :
    (gaAffineGroupPoints x (Multiplicative.ofAdd c))⁻¹ =
      gaAffineGroupPoints x (Multiplicative.ofAdd (-c)) := by
  rw [ofAdd_neg, map_inv]

/-- `n⁻¹ = x(-1) y(1) x(-1) = n(-1)`, by the group law of the additive
subgroups. -/
theorem rootReflectionPoint_inv (x y : B →ₐc[K] SymmetricAlgebra K K) :
    (rootReflectionPoint x y)⁻¹ = rootReflectionPointAt x y (-1) := by
  simp only [rootReflectionPoint, rootReflectionPointAt, mul_inv_rev,
    gaAffineGroupPoints_ofAdd_inv, inv_neg, inv_one, neg_neg, mul_assoc]

variable [CharZero K] [Algebra.FiniteType K B]

namespace IsRootSl2Pair

variable {π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))}
  {α : Multiplicative (ι →₀ ℤ)} {x y : B →ₐc[K] SymmetricAlgebra K K}

/-- The reflection point of an `sl₂`-normalized pair acts on the torus tangent
image by `t ↦ t - dα(t) ⁅dx, dy⁆`. -/
theorem adjoint_rootReflectionPoint (hp : IsRootSl2Pair π α x y)
    (hπ : Function.Surjective π) (t : diagonalizableTangentImage π) :
    affineGroupAdjointRepresentation (rootReflectionPoint x y) (t : 𝔤) =
      (t : 𝔤) - characterDifferentialOnImage π hπ α t •
        ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆ := by
  have hvx := RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ α _ hp.tangent_mem t
  have hvy := RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ α⁻¹ _
    hp.partner_tangent_mem t
  rw [characterDifferentialOnImage_inv, LinearMap.neg_apply] at hvy
  exact gaSl2PointProduct_adjoint_reflection x y _ (t : 𝔤) _ hp.isSl2Triple hvx hvy

/-- The reflection point maps the torus tangent image into itself. -/
theorem adjoint_rootReflectionPoint_mem (hp : IsRootSl2Pair π α x y)
    (hπ : Function.Surjective π) (t : diagonalizableTangentImage π) :
    affineGroupAdjointRepresentation (rootReflectionPoint x y) (t : 𝔤) ∈
      diagonalizableTangentImage π := by
  rw [hp.adjoint_rootReflectionPoint hπ t]
  exact (diagonalizableTangentImage π).sub_mem t.property
    ((diagonalizableTangentImage π).smul_mem _ hp.bracket_mem)

/-- The reflection point maps the torus tangent image onto itself: its action
there is an involution because `dα(⁅dx, dy⁆) = 2`. -/
theorem adjoint_rootReflectionPoint_onto (hp : IsRootSl2Pair π α x y)
    (hπ : Function.Surjective π) (t : diagonalizableTangentImage π) :
    ∃ u : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation (rootReflectionPoint x y) (u : 𝔤) = (t : 𝔤) := by
  let H := diagonalizableTangentImage π
  let h : H := ⟨_, hp.bracket_mem⟩
  let χ := characterDifferentialOnImage π hπ α
  have hh : χ h = 2 := hp.characterDifferential_bracket hπ
  let R : H → H := fun s => ⟨_, hp.adjoint_rootReflectionPoint_mem hπ s⟩
  have hR (s : H) : R s = s - χ s • h := by
    apply Subtype.ext
    exact hp.adjoint_rootReflectionPoint hπ s
  have hR2 : R (R t) = t := by
    rw [hR (R t), hR t]
    simp only [map_sub, map_smul, hh]
    module
  exact ⟨R t, congrArg Subtype.val hR2⟩

/-- **Torus normalization.** For every `K`-point `g`, the conjugate `n g n⁻¹` by
the reflection point of an `sl₂`-normalized pair lies in the torus points `T(K)`
iff `g` does. -/
theorem rootReflection_conj_torus_iff (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) (g : WithConv (B →ₐ[K] K)) :
    rootReflectionPoint x y * g * (rootReflectionPoint x y)⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K) := by
  have h := TorusPointSubgroup.mem_iff_of_adjoint_tangent_bijective π hπ I hker
    (rootReflectionPoint x y) (hp.adjoint_rootReflectionPoint_mem hπ)
    (hp.adjoint_rootReflectionPoint_onto hπ) (A := K) g
  have hs : WithConv.toConv ((IsScalarTower.toAlgHom K K K).comp
      (rootReflectionPoint x y).ofConv) = rootReflectionPoint x y := by
    apply WithConv.ofConv_injective
    ext a
    rfl
  simpa only [hs] using h

/-- The reflection point of an `sl₂`-normalized pair lies in the normalizer of
the torus point subgroup `T(K)`. -/
theorem rootReflectionPoint_mem_normalizer (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) :
    rootReflectionPoint x y ∈ Subgroup.normalizer
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K) : Set (WithConv (B →ₐ[K] K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  exact (hp.rootReflection_conj_torus_iff I hπ hker g).symm

/-- Conjugation by the reflection point maps `T(K)` onto `T(K)`. -/
theorem rootReflectionPoint_map_torusPoints (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) :
    (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K)).map (MulAut.conj (rootReflectionPoint x y)).toMonoidHom =
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) := by
  let n := rootReflectionPoint x y
  have hiff := hp.rootReflection_conj_torus_iff I hπ hker
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (hiff t).mpr ht
  · intro hg
    refine ⟨n⁻¹ * g * n, (hiff _).mp ?_, ?_⟩
    · simpa only [n, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hg
    · change n * (n⁻¹ * g * n) * n⁻¹ = g
      group

variable [IsAlgClosed K]

/-- **Rescaled reflection points.** For every `c ≠ 0`,
`x(c) y(-c⁻¹) x(c) = t · x(1) y(-1) x(1)` for some `t ∈ T(K)`.
A torus point `D` with `α(D) = c` conjugates `n` to `n(c)`, and
`n(c) = D (n D⁻¹ n⁻¹) n` with `n D⁻¹ n⁻¹ ∈ T(K)`. -/
theorem rootReflectionPointAt_mem_torus_mul (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) {c : K} (hc : c ≠ 0) :
    ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      rootReflectionPointAt x y c = t * rootReflectionPoint x y := by
  obtain ⟨s, hs⟩ := exists_torusPoint_character_value (K := K) α (hp.ne_one hπ) c hc
  let D := TauCeti.AlgHom.mapDomain π s
  set n := rootReflectionPoint x y with hn
  have hsinv : s.ofConv (MonoidAlgebra.single α⁻¹ 1) = c⁻¹ := by
    rw [torusPoint_character_inv, hs]
  have hDx (u : K) : D * gaAffineGroupPoints x (Multiplicative.ofAdd u) * D⁻¹ =
      gaAffineGroupPoints x (Multiplicative.ofAdd (c * u)) := by
    rw [GaAffineGroupPoints.conjugate_of_character_weight π α s x hp.tangent_mem u, hs]
  have hDy (u : K) : D * gaAffineGroupPoints y (Multiplicative.ofAdd u) * D⁻¹ =
      gaAffineGroupPoints y (Multiplicative.ofAdd (c⁻¹ * u)) := by
    rw [GaAffineGroupPoints.conjugate_of_character_weight π α⁻¹ s y
      hp.partner_tangent_mem u, hsinv]
  have hconj : D * n * D⁻¹ = rootReflectionPointAt x y c := by
    have hsplit : D * n * D⁻¹ =
        (D * gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) * D⁻¹) *
          (D * gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) * D⁻¹) *
            (D * gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) * D⁻¹) := by
      rw [hn, rootReflectionPoint]
      group
    rw [hsplit, hDx, hDy, mul_one, mul_neg_one, rootReflectionPointAt]
  have hDT : D ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
      (CommAlgCat.of K K) := mapDomain_mem_torusPoints I π hπ hker s
  have hmid : n * D⁻¹ * n⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) :=
    (hp.rootReflection_conj_torus_iff I hπ hker D⁻¹).mpr (inv_mem hDT)
  refine ⟨D * (n * D⁻¹ * n⁻¹), mul_mem hDT hmid, ?_⟩
  rw [← hconj]
  group

/-- For every `c ≠ 0` the rescaled reflection point `n(c)` also normalizes
`T(K)`: `n(c) g n(c)⁻¹ ∈ T(K) ↔ g ∈ T(K)`. -/
theorem RootReflectionPointAt.conj_mem_torusPoints_iff (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) {c : K} (hc : c ≠ 0)
    (g : WithConv (B →ₐ[K] K)) :
    rootReflectionPointAt x y c * g * (rootReflectionPointAt x y c)⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K) := by
  obtain ⟨t, ht, h⟩ := hp.rootReflectionPointAt_mem_torus_mul I hπ hker hc
  rw [h, ← hp.rootReflection_conj_torus_iff I hπ hker g,
    show t * rootReflectionPoint x y * g * (t * rootReflectionPoint x y)⁻¹ =
      t * (rootReflectionPoint x y * g * (rootReflectionPoint x y)⁻¹) * t⁻¹ by group,
    mul_mem_cancel_right (inv_mem ht), mul_mem_cancel_left ht]

/-- `n⁻¹ ∈ T(K) · n`. -/
theorem rootReflectionPoint_inv_mem_torus_mul (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) :
    ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      (rootReflectionPoint x y)⁻¹ = t * rootReflectionPoint x y := by
  rw [rootReflectionPoint_inv]
  exact hp.rootReflectionPointAt_mem_torus_mul I hπ hker (neg_ne_zero.mpr one_ne_zero)

/-- `n² ∈ T(K)`. -/
theorem rootReflectionPoint_sq_mem_torusPoints (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) :
    rootReflectionPoint x y ^ 2 ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) := by
  obtain ⟨t, ht, h⟩ := hp.rootReflectionPoint_inv_mem_torus_mul I hπ hker
  have ht' : t = (rootReflectionPoint x y)⁻¹ * (rootReflectionPoint x y)⁻¹ :=
    eq_mul_inv_of_mul_eq h.symm
  have hsq : rootReflectionPoint x y ^ 2 = t⁻¹ := by
    rw [ht', pow_two, mul_inv_rev, inv_inv]
  rw [hsq]
  exact inv_mem ht

/-- **Rank-one Bruhat relation.** For every `d ≠ 0` there is `t ∈ T(K)` with
`y(d) = x(d⁻¹) · t · n · x(d⁻¹)`, where `n = x(1) y(-1) x(1)`. -/
theorem partner_point_eq_mul_torus_mul (hp : IsRootSl2Pair π α x y)
    (I : HopfIdeal K B) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) {d : K} (hd : d ≠ 0) :
    ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K),
      gaAffineGroupPoints y (Multiplicative.ofAdd d) =
        gaAffineGroupPoints x (Multiplicative.ofAdd d⁻¹) * t * rootReflectionPoint x y *
          gaAffineGroupPoints x (Multiplicative.ofAdd d⁻¹) := by
  obtain ⟨t, ht, h⟩ := hp.rootReflectionPointAt_mem_torus_mul I hπ hker
    (neg_ne_zero.mpr (inv_ne_zero hd))
  refine ⟨t, ht, ?_⟩
  rw [rootReflectionPointAt, inv_neg, neg_neg, inv_inv] at h
  have hX : gaAffineGroupPoints x (Multiplicative.ofAdd d⁻¹) =
      (gaAffineGroupPoints x (Multiplicative.ofAdd (-d⁻¹)))⁻¹ := by
    rw [gaAffineGroupPoints_ofAdd_inv, neg_neg]
  rw [hX, mul_assoc _ t, ← h]
  group

end IsRootSl2Pair

end ReductiveGroups
