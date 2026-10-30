import OrbitComplexity.ReductiveGroups.Lie.Roots.RootAdjointRepresentation
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentOneParameterSubgroup
import OrbitComplexity.ReductiveGroups.Lie.Roots.CanonicalBooleanActorsCommute
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Root Product Conjugation

Ordered root-adjoint products as conjugation by units. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

/-- The equality is

```lean
Commute (associativeExponential (K := K) x)
      (associativeExponential (K := K) y)
```
-/
theorem associativeExponential_commute {x y : A}
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hxy : Commute x y) :
    Commute (associativeExponential (K := K) x)
      (associativeExponential (K := K) y) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  change IsNilpotent.exp x * IsNilpotent.exp y =
    IsNilpotent.exp y * IsNilpotent.exp x
  rw [← IsNilpotent.exp_add_of_commute hxy hx hy,
    ← IsNilpotent.exp_add_of_commute hxy.symm hy hx, add_comm]

/-- For these parameters,

```lean
Commute (nilpotentExponentialUnit x hx t) (nilpotentExponentialUnit y hy s)
```
-/
theorem nilpotentExponentialUnit_commute {x y : A}
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hxy : Commute x y) (t s : K) :
    Commute (nilpotentExponentialUnit x hx t) (nilpotentExponentialUnit y hy s) := by
  apply Units.ext
  exact associativeExponential_commute (hx.smul t) (hy.smul s)
    ((hxy.smul_left t).smul_right s)

section Ordered
variable {V ι : Type*} [AddCommGroup V] [Module K V]

omit [CharZero K] in
/-- Intertwining every factor with conjugation intertwines the ordered product.
Neither factor commutation nor injectivity of the representation is needed. -/
theorem ordered_conjugation_intertwining
    (f : V →ₗ[K] A) (F : ι → Module.End K V) (u : ι → Aˣ)
    (h : ∀ i y, f (F i y) = (u i : A) * f y * ((u i)⁻¹ : Aˣ))
    (l : List ι) (y : V) :
    f ((l.map F).prod y) =
      ((l.map u).prod : A) * f y * (((l.map u).prod)⁻¹ : Aˣ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [h, ih]
    simp only [mul_inv_rev, Units.val_mul]
    simp only [mul_assoc]

end Ordered

/-- The equality is

```lean
(l.map (fun u => u⁻¹)).prod = l.prod⁻¹
```
-/
theorem commuting_list_prod_inv {G : Type*} [Group G]
    (l : List G) (hc : l.Pairwise Commute) :
    (l.map (fun u => u⁻¹)).prod = l.prod⁻¹ := by
  have hi : (l.map (fun u => u⁻¹)).Pairwise Commute := by
    rw [List.pairwise_map]
    exact hc.imp (fun h => h.inv_inv)
  rw [List.prod_inv_reverse]
  exact (List.reverse_perm _).symm.prod_eq' hi

variable {L : Type*} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsAlgClosed K] [FiniteDimensional K A]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The finite adjoint product is represented by the same ordered
product of negative-parameter exponential units, with its inverse. -/
theorem rootAdjointProduct_representation {ι : Type*}
    (χ : ι → H → K) (hχ : ∀ i, χ i ≠ 0)
    (x : ι → L) (hx : ∀ i, x i ∈ rootSpace H (χ i))
    (f : L →ₗ⁅K⁆ A) (n : ι → K) (l : List ι) (y : L) :
    f ((l.map (fun i =>
      (rootAdjointExponential H (χ i) (hχ i) (x i) (hx i) (n i)).toLinearMap)).prod y) =
      ((l.map (fun i => nilpotentExponentialUnit (f (x i))
        (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f (hχ i) (hx i)) (-n
          i))).prod : A) *
      f y * (((l.map (fun i => nilpotentExponentialUnit (f (x i))
        (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f (hχ i) (hx i))
        (-n i))).prod)⁻¹ : Aˣ) := by
  apply ordered_conjugation_intertwining
  intro i z
  change f (rootAdjointExponential H (χ i) (hχ i) (x i) (hx i) (n i) z) =
    associativeExponential (K := K) ((-n i) • f (x i)) * f z *
      associativeExponential (K := K) ((-(-n i)) • f (x i))
  rw [neg_neg]
  exact RootAdjointExponential.finite_representation H (χ i) (hχ i) (x i) (hx i) f (n i) z

variable [LieAlgebra.IsKilling K L]

/-- Boolean root vectors yield commuting exponential units in every finite
associative representation. Commutation is derived from the roots. -/
theorem boolean_represented_root_units_commute
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (word : List b.support) (hword : word.Nodup)
    (α β : H.root)
    (hα : α ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (x : H.root → L) (hx : ∀ γ : H.root, x γ ∈ rootSpace H (γ : Weight K H L))
    (f : L →ₗ⁅K⁆ A) (t s : K) :
    Commute
      (nilpotentExponentialUnit (f (x α))
        (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f
          (canonicalRootWeight_realization H α).2 (hx α)) t)
      (nilpotentExponentialUnit (f (x β))
        (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f
          (canonicalRootWeight_realization H β).2 (hx β)) s) := by
  apply nilpotentExponentialUnit_commute
  have h := canonical_boolean_root_vectors_commute H b word hword α β hα hβ
    (x α) (x β) (hx α) (hx β)
  have hm := f.map_lie (x α) (x β)
  rw [h, map_zero] at hm
  change 0 = f (x α) * f (x β) - f (x β) * f (x α) at hm
  exact sub_eq_zero.mp hm.symm

/-- the inverse-product convention: the negative adjoint
exponentials represent conjugation by the inverse of the positive unit product. -/
theorem RootProductConjugation.inverse_representation
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (word : List b.support) (hword : word.Nodup)
    (l : List H.root)
    (hl : ∀ γ ∈ l, γ ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (x : H.root → L) (hx : ∀ γ : H.root, x γ ∈ rootSpace H (γ : Weight K H L))
    (f : L →ₗ⁅K⁆ A) (n : H.root → K) (y : L) :
    let u : H.root → Aˣ := fun γ => nilpotentExponentialUnit (f (x γ))
      (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f
        (canonicalRootWeight_realization H γ).2 (hx γ)) (n γ)
    f ((l.map (fun γ : H.root => (rootAdjointExponential H
      ((γ : Weight K H L) : H → K) (canonicalRootWeight_realization H γ).2
      (x γ) (hx γ) (n γ)).toLinearMap)).prod y) =
      (((l.map u).prod)⁻¹ : Aˣ) * f y * ((l.map u).prod : A) := by
  dsimp only
  let u : H.root → Aˣ := fun γ => nilpotentExponentialUnit (f (x γ))
    (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f
      (canonicalRootWeight_realization H γ).2 (hx γ)) (n γ)
  have hc : (l.map u).Pairwise Commute := by
    rw [List.pairwise_map]
    apply List.pairwise_of_forall_mem_list
    intro α hα β hβ
    exact boolean_represented_root_units_commute H b word hword α β (hl α hα) (hl β hβ)
      x hx f (n α) (n β)
  have heq := rootAdjointProduct_representation H
    (fun γ : H.root => ((γ : Weight K H L) : H → K))
    (fun γ => (canonicalRootWeight_realization H γ).2) x hx f n l y
  have hlist : l.map (fun γ => nilpotentExponentialUnit (f (x γ))
      (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f
        (canonicalRootWeight_realization H γ).2 (hx γ)) (-n γ)) =
      (l.map u).map (fun v => v⁻¹) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro γ _
    apply Units.ext
    rfl
  rw [hlist, commuting_list_prod_inv _ hc, inv_inv] at heq
  exact heq

end ReductiveGroups
