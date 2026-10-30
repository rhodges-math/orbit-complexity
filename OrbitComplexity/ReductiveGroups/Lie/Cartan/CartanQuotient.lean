import Mathlib.Algebra.Lie.CartanSubalgebra

/-!
# Cartan Quotient

Cartan subalgebras contain the center, and descend along surjective
Lie maps whose kernel they contain. This preserves the original quotient. -/

noncomputable section
namespace ReductiveGroups

variable {R L Q : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing Q] [LieAlgebra R Q]

/-- Every central vector lies in each Cartan subalgebra. -/
theorem center_le_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieAlgebra.center R L : LieSubalgebra R L) ≤ H := by
  intro z hz
  rw [← LieSubalgebra.IsCartanSubalgebra.self_normalizing (H := H)]
  apply (H.mem_normalizer_iff' z).mpr
  intro y _
  have hzero := (LieModule.mem_maxTrivSubmodule (R := R) (L := L) (M := L) z).mp hz y
  rw [hzero]
  exact H.zero_mem

/-- A Cartan subalgebra descends to the image under a surjective Lie
map when it contains that map's kernel. -/
theorem cartan_map_of_surjective
    (f : L →ₗ⁅R⁆ Q) (hf : Function.Surjective f)
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    (hker : (f.ker : LieSubalgebra R L) ≤ H) :
    (H.map f).IsCartanSubalgebra := by
  have hpre (x : L) : f x ∈ H.map f ↔ x ∈ H := by
    constructor
    · intro hx
      obtain ⟨y, hy, hfy⟩ := (H.mem_map f (f x)).mp hx
      have hdiff : x - y ∈ (f.ker : LieSubalgebra R L) := by
        change f (x - y) = 0
        rw [map_sub, hfy, sub_self]
      simpa only [sub_add_cancel] using H.add_mem (hker hdiff) hy
    · intro hx
      exact (H.mem_map f (f x)).mpr ⟨x, hx, rfl⟩
  let fH : H →ₗ⁅R⁆ H.map f :=
    { toFun := fun y => ⟨f y, (hpre y).mpr y.property⟩
      map_add' := by intros; apply Subtype.ext; apply map_add
      map_smul' := by intros; apply Subtype.ext; apply map_smul
      map_lie' := by intros; apply Subtype.ext; apply LieHom.map_lie }
  have hfH : Function.Surjective fH := by
    intro q
    obtain ⟨x, hx, hfx⟩ := (H.mem_map f q).mp q.property
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  refine ⟨hfH.lieAlgebra_isNilpotent, le_antisymm ?_ (H.map f).le_normalizer⟩
  intro q hq
  obtain ⟨x, rfl⟩ := hf q
  apply (hpre x).mpr
  rw [← LieSubalgebra.IsCartanSubalgebra.self_normalizing (H := H)]
  apply (H.mem_normalizer_iff x).mpr
  intro y hy
  apply (hpre ⁅x, y⁆).mp
  rw [LieHom.map_lie]
  exact ((H.map f).mem_normalizer_iff (f x)).mp hq (f y) ((hpre y).mpr hy)

end ReductiveGroups
