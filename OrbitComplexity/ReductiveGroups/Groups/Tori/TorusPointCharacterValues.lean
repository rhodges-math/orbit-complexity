import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Torus Point Character Values

Ground-field points of a fixed closed split torus of an affine group, and
prescribed character values at such points.

The torus is given by a Hopf ideal `I` of the coordinate algebra `B` together
with a surjective bialgebra map `π : B → K[M]`, `M = ℤ^(ι)` written
multiplicatively, whose kernel is exactly `I`. Its `K`-points are the subgroup
`quotientPointsSubgroup … I (CommAlgCat.of K K)` of the convolution group of
`K`-points of `B`; the value of a point `t` of `K[M]` at a character `χ` is
`t.ofConv (MonoidAlgebra.single χ 1)`.

Over an algebraically closed field, values at `ℤ`-linearly independent
characters may be prescribed arbitrarily in `Kˣ`. The proof uses only that
`Kˣ` is a divisible abelian group, hence an injective `ℤ`-module (Baer). -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

universe u

section Points

variable {K B ι : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- A `K`-point of the original group lies in the point subgroup cut out by the
torus ideal `I` exactly when it is the image `mapDomain π t` of a `K`-point `t`
of the split torus `K[M]`. The kernel of `π` is `I` and `π` is surjective. -/
theorem mem_torusPoints_iff
    (I : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K K) ↔
      ∃ t : WithConv (MonoidAlgebra K M →ₐ[K] K), g = TauCeti.AlgHom.mapDomain π t := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hg
    have hπker : RingHom.ker π.toAlgHom.toRingHom ≤ RingHom.ker g.ofConv.toRingHom := by
      intro b hb
      apply RingHom.mem_ker.mpr
      exact hg b ((hker b).mp (RingHom.mem_ker.mp hb))
    refine ⟨toConv (_root_.AlgHom.liftOfSurjective π.toAlgHom hπ g.ofConv hπker), ?_⟩
    apply WithConv.ofConv_injective
    exact (_root_.AlgHom.liftOfSurjective_comp π.toAlgHom hπ g.ofConv hπker).symm
  · rintro ⟨t, rfl⟩ a ha
    change t.ofConv (π a) = 0
    rw [(hker a).mpr ha, map_zero]

/-- Every point `mapDomain π t` lies in the torus point subgroup. -/
theorem mapDomain_mem_torusPoints
    (I : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) :
    TauCeti.AlgHom.mapDomain π t ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) :=
  (mem_torusPoints_iff I π hπ hker _).mpr ⟨t, rfl⟩

end Points

section Characters

variable {K ι : Type u} [Field K]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The value of a torus point at an inverse character is the inverse value. -/
theorem torusPoint_character_inv (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) (α : M) :
    t.ofConv (MonoidAlgebra.single α⁻¹ 1) = (t.ofConv (MonoidAlgebra.single α 1))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
    ← MonoidAlgebra.one_def, map_one]

/-- In an algebraically closed field every unit has an `n`-th root for every
nonzero integer `n`. -/
private theorem units_zpow_surjective [IsAlgClosed K] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun u : Kˣ => u ^ n) := by
  intro u
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact u.ne_zero hz.symm
  let v := Units.mk0 z hz0
  have hv : v ^ n.natAbs = u := Units.ext (by simp [v, hz])
  rcases Int.natAbs_eq n with h | h
  · refine ⟨v, ?_⟩
    change v ^ n = u
    rw [h, zpow_natCast, hv]
  · refine ⟨v⁻¹, ?_⟩
    change v⁻¹ ^ n = u
    rw [h, zpow_neg, zpow_natCast, inv_pow, inv_inv, hv]

/-- **Prescribed character values.** Over an algebraically closed field, for a
family of characters `χ s` of the split torus that is linearly independent over
`ℤ` in `ι →₀ ℤ`, and arbitrary units `c s`, there is a `K`-point `t` of the torus
with `t(χ s) = c s` for every `s`. -/
theorem exists_torusPoint_character_values [IsAlgClosed K]
    {S : Type*} (χ : S → M)
    (hχ : LinearIndependent ℤ (fun s => Multiplicative.toAdd (χ s)))
    (c : S → Kˣ) :
    ∃ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      ∀ s, t.ofConv (MonoidAlgebra.single (χ s) 1) = c s := by
  let _ : DivisibleBy (Additive Kˣ) ℤ :=
    divisibleByOfSMulRightSurj (Additive Kˣ) ℤ (fun {n} hn a => by
      obtain ⟨v, hv⟩ := units_zpow_surjective (K := K) hn (Additive.toMul a)
      exact ⟨Additive.ofMul v, by
        change n • Additive.ofMul v = a
        rw [← ofMul_zpow]
        exact congrArg Additive.ofMul hv⟩)
  let v : S → (ι →₀ ℤ) := fun s => Multiplicative.toAdd (χ s)
  let N := Submodule.span ℤ (Set.range v)
  let b : Module.Basis S ℤ N := Module.Basis.span hχ
  let g : N →ₗ[ℤ] Additive Kˣ := b.constr ℤ (fun s => Additive.ofMul (c s))
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Kˣ)).extension_property
    N.subtype N.injective_subtype g
  let φ : M →* K :=
    { toFun := fun m => ((Additive.toMul (h (Multiplicative.toAdd m)) : Kˣ) : K)
      map_one' := by simp
      map_mul' := by intro a b; simp }
  refine ⟨toConv (MonoidAlgebra.lift K K M φ), fun s => ?_⟩
  change MonoidAlgebra.lift K K M φ (MonoidAlgebra.single (χ s) 1) = c s
  rw [MonoidAlgebra.lift_single, one_smul]
  have hs : h (v s) = Additive.ofMul (c s) := by
    have hc := LinearMap.congr_fun hh (b s)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, b, g,
      Module.Basis.constr_basis] at hc
    rw [Module.Basis.span_apply] at hc
    exact hc
  change ((Additive.toMul (h (v s)) : Kˣ) : K) = c s
  rw [hs]
  rfl

/-- A single nonidentity character of the split torus takes every nonzero value
at some `K`-point, over an algebraically closed field. -/
theorem exists_torusPoint_character_value [IsAlgClosed K]
    (α : M) (hα : α ≠ 1) (c : K) (hc : c ≠ 0) :
    ∃ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      t.ofConv (MonoidAlgebra.single α 1) = c := by
  have hli : LinearIndependent ℤ (fun _ : Unit => Multiplicative.toAdd α) := by
    rw [linearIndependent_unique_iff]
    simpa using hα
  obtain ⟨t, ht⟩ := exists_torusPoint_character_values (K := K)
    (fun _ : Unit => α) hli (fun _ => Units.mk0 c hc)
  exact ⟨t, ht ()⟩

end Characters

end ReductiveGroups
