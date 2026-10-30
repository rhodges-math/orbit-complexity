import OrbitComplexity.ReductiveGroups.Lie.Roots.RootSpaceCenterQuotient
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CartanQuotient
import Mathlib.Algebra.Lie.Weights.Basic

/-!
# Center Quotient Root Spaces

Generalized root spaces under the quotient by the center. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieModule

/-- The equality is

```lean
(genWeightSpace M χ).map f = genWeightSpace N χ
```
-/
theorem CenterQuotientRootSpaces.lieModuleHom_map_genWeightSpace
    {K H M N : Type*} [Field K] [IsAlgClosed K]
    [LieRing H] [LieAlgebra K H] [LieRing.IsNilpotent H]
    [AddCommGroup M] [Module K M] [LieRingModule H M] [LieModule K H M]
    [AddCommGroup N] [Module K N] [LieRingModule H N] [LieModule K H N]
    [FiniteDimensional K M]
    (f : M →ₗ⁅K,H⁆ N) (hf : Function.Surjective f) (χ : H → K) :
    (genWeightSpace M χ).map f = genWeightSpace N χ := by
  have hspan : ⨆ ψ : H → K, (genWeightSpace M ψ).map f = ⊤ := by
    rw [← LieSubmodule.map_iSup, iSup_genWeightSpace_eq_top K H M]
    simpa only [LieModuleHom.map_top] using (LieModuleHom.range_eq_top f).mpr hf
  have hi : iSupIndep (fun ψ : H → K => genWeightSpace N ψ) :=
    iSupIndep_genWeightSpace K H N
  exact congrFun ((hi.le_iff_eq_of_iSup_eq_top hspan).mp
    (fun ψ => map_genWeightSpace_le f)) χ

variable {K L : Type*} [Field K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-- The image of a Cartan subalgebra `H` of `L` in the quotient `L ⧸ center K L`. -/
abbrev centerQuotientCartan : LieSubalgebra K (L ⧸ LieAlgebra.center K L) :=
  H.map (centerQuotientLieHom (K := K))

/-- The surjective Lie algebra homomorphism from `H` onto its image `centerQuotientCartan H` in `L ⧸
center K L`. -/
def centerQuotientCartanMap : H →ₗ⁅K⁆ centerQuotientCartan H where
  toFun h := ⟨centerQuotientLieHom (K := K) h,
    (H.mem_map _ _).mpr ⟨h, h.property, rfl⟩⟩
  map_add' := by intros; apply Subtype.ext; simp
  map_smul' := by intros; apply Subtype.ext; simp
  map_lie' := by intros; apply Subtype.ext; simp

omit [IsAlgClosed K] [FiniteDimensional K L] [H.IsCartanSubalgebra] in
/-- The map is surjective:

```lean
Function.Surjective (centerQuotientCartanMap H)
```
-/
theorem centerQuotientCartanMap_surjective :
    Function.Surjective (centerQuotientCartanMap H) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := (H.mem_map _ _).mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The image of a Cartan subalgebra in the center quotient is nilpotent. -/
instance centerQuotientCartan_isNilpotent :
    LieRing.IsNilpotent (centerQuotientCartan H) :=
  (centerQuotientCartanMap_surjective H).lieAlgebra_isNilpotent

private def centerQuotientAsCartanModuleHom :
    letI := LieRingModule.compLieHom (L ⧸ LieAlgebra.center K L)
      (centerQuotientCartanMap H)
    letI := LieModule.compLieHom (L ⧸ LieAlgebra.center K L)
      (centerQuotientCartanMap H)
    L →ₗ⁅K,H⁆ (L ⧸ LieAlgebra.center K L) := by
  letI := LieRingModule.compLieHom (L ⧸ LieAlgebra.center K L)
    (centerQuotientCartanMap H)
  letI := LieModule.compLieHom (L ⧸ LieAlgebra.center K L)
    (centerQuotientCartanMap H)
  exact {
    centerQuotientLieHom (K := K).toLinearMap with
    map_lie' := by
      intro h x
      change centerQuotientLieHom (K := K) ⁅(h : L), x⁆ =
        ⁅centerQuotientLieHom (K := K) (h : L),
          centerQuotientLieHom (K := K) x⁆
      exact LieHom.map_lie _ _ _ }

omit [IsAlgClosed K] [FiniteDimensional K L] in
private theorem centerQuotient_weight_mem_iff
    (χ : centerQuotientCartan H → K)
    (x : L ⧸ LieAlgebra.center K L) :
    letI := LieRingModule.compLieHom (L ⧸ LieAlgebra.center K L)
        (centerQuotientCartanMap H)
    letI := LieModule.compLieHom (L ⧸ LieAlgebra.center K L)
        (centerQuotientCartanMap H)
    (x ∈ genWeightSpace (L ⧸ LieAlgebra.center K L)
      (fun h : H => χ (centerQuotientCartanMap H h))) ↔
      x ∈ rootSpace (centerQuotientCartan H) χ := by
  rw [mem_genWeightSpace, mem_genWeightSpace]
  constructor
  · intro hx y
    obtain ⟨h, rfl⟩ := centerQuotientCartanMap_surjective H y
    obtain ⟨k, hk⟩ := hx h
    exact ⟨k, hk⟩
  · intro hx h
    obtain ⟨k, hk⟩ := hx (centerQuotientCartanMap H h)
    exact ⟨k, hk⟩

/-- The center quotient maps each original root space into the
corresponding root space of the image Cartan. -/
def centerQuotientRootSpaceMap
    (χ : centerQuotientCartan H → K) :
    rootSpace H (fun h => χ (centerQuotientCartanMap H h)) →ₗ[K]
      rootSpace (centerQuotientCartan H) χ := by
  letI := LieRingModule.compLieHom (L ⧸ LieAlgebra.center K L)
    (centerQuotientCartanMap H)
  letI := LieModule.compLieHom (L ⧸ LieAlgebra.center K L)
    (centerQuotientCartanMap H)
  let f := centerQuotientAsCartanModuleHom H
  exact (f.toLinearMap.restrict
    (fun x hx => (centerQuotient_weight_mem_iff H χ (f x)).mp
      (map_genWeightSpace_le f (LieSubmodule.mem_map_of_mem hx))))

/-- The map is surjective:

```lean
Function.Surjective (centerQuotientRootSpaceMap H χ)
```
-/
theorem centerQuotientRootSpaceMap_surjective
    (χ : centerQuotientCartan H → K) :
    Function.Surjective (centerQuotientRootSpaceMap H χ) := by
  let _ := LieRingModule.compLieHom (L ⧸ LieAlgebra.center K L)
    (centerQuotientCartanMap H)
  let _ := LieModule.compLieHom (L ⧸ LieAlgebra.center K L)
    (centerQuotientCartanMap H)
  let f := centerQuotientAsCartanModuleHom H
  have hf : Function.Surjective f := centerQuotientLieHom_surjective
  have heq := CenterQuotientRootSpaces.lieModuleHom_map_genWeightSpace f hf
    (fun h => χ (centerQuotientCartanMap H h))
  intro y
  have hy : (y : L ⧸ LieAlgebra.center K L) ∈
      genWeightSpace (L ⧸ LieAlgebra.center K L)
        (fun h => χ (centerQuotientCartanMap H h)) :=
    (centerQuotient_weight_mem_iff H χ y).mpr y.property
  obtain ⟨x, hx, hxy⟩ := (LieSubmodule.mem_map (y : L ⧸ LieAlgebra.center K L)).mp
    (heq.symm ▸ hy)
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

omit [IsAlgClosed K] [FiniteDimensional K L] in
/-- The map is injective:

```lean
Function.Injective (centerQuotientRootSpaceMap H χ)
```
-/
theorem centerQuotientRootSpaceMap_injective
    (χ : centerQuotientCartan H → K) (hχ : χ ≠ 0) :
    Function.Injective (centerQuotientRootSpaceMap H χ) := by
  have hcomp : (fun h : H => χ (centerQuotientCartanMap H h)) ≠ 0 := by
    intro hz
    apply hχ
    funext y
    obtain ⟨h, rfl⟩ := centerQuotientCartanMap_surjective H y
    exact congrFun hz h
  intro x y hxy
  apply centerQuotient_injective_on_rootSpace H _ hcomp
  exact congrArg Subtype.val hxy

/-- A nonzero root space of the original Lie algebra is linearly equivalent
to the corresponding root space in its quotient by the center. -/
def centerQuotientRootSpaceEquiv
    (χ : centerQuotientCartan H → K) (hχ : χ ≠ 0) :
    rootSpace H (fun h => χ (centerQuotientCartanMap H h)) ≃ₗ[K]
      rootSpace (centerQuotientCartan H) χ :=
  LinearEquiv.ofBijective (centerQuotientRootSpaceMap H χ)
    ⟨centerQuotientRootSpaceMap_injective H χ hχ,
      centerQuotientRootSpaceMap_surjective H χ⟩

/-- The equality is

```lean
((centerQuotientRootSpaceEquiv H χ hχ x :
      rootSpace (centerQuotientCartan H) χ) : L ⧸ LieAlgebra.center K L) =
      centerQuotientLieHom (K := K) (x : L)
```
-/
@[simp] theorem centerQuotientRootSpaceEquiv_apply
    (χ : centerQuotientCartan H → K) (hχ : χ ≠ 0)
    (x : rootSpace H (fun h => χ (centerQuotientCartanMap H h))) :
    ((centerQuotientRootSpaceEquiv H χ hχ x :
      rootSpace (centerQuotientCartan H) χ) : L ⧸ LieAlgebra.center K L) =
      centerQuotientLieHom (K := K) (x : L) := rfl

end ReductiveGroups
