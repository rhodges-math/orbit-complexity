import OrbitComplexity.ReductiveGroups.Groups.Representations.TriangularSolvable
import OrbitComplexity.ReductiveGroups.Groups.Solvable.ConnectedGeneratedSolvability

/-!
# Generated Triangular Solvability

A common faithful triangular representation of the generators
proves solvability of their generated subgroup and of its closed quotient. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory WithConv

variable {R G : Type*} [CommRing R] [Group G] {n : ℕ}

/-- For these parameters,

```lean
matrixUpperGap 0 (1 : Matrix (Fin n) (Fin n) R)
```
-/
theorem matrixUpperGap_one : matrixUpperGap 0 (1 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  apply Matrix.one_apply_ne
  intro heq
  subst j
  omega

/-- Both directions are retained so subgroup closure needs no separate
matrix inverse-triangularity theorem. -/
def triangularRepresentationSubgroup (ρ : G →* (Matrix (Fin n) (Fin n) R)ˣ) :
    Subgroup G where
  carrier := {g | matrixUpperGap 0 (ρ g : Matrix (Fin n) (Fin n) R) ∧
    matrixUpperGap 0 (ρ g⁻¹ : Matrix (Fin n) (Fin n) R)}
  one_mem' := by
    change matrixUpperGap 0 (ρ 1 : Matrix (Fin n) (Fin n) R) ∧
      matrixUpperGap 0 (ρ (1 : G)⁻¹ : Matrix (Fin n) (Fin n) R)
    simpa only [inv_one, map_one, Units.val_one] using
      And.intro (matrixUpperGap_one (R := R) (n := n))
        (matrixUpperGap_one (R := R) (n := n))
  mul_mem' := by
    intro a b ha hb
    constructor
    · simpa only [map_mul, Units.val_mul] using matrixUpperGap_mul ha.1 hb.1
    · simpa only [mul_inv_rev, map_mul, Units.val_mul] using matrixUpperGap_mul hb.2 ha.2
  inv_mem' := by
    intro a ha
    change matrixUpperGap 0 (ρ a⁻¹ : Matrix (Fin n) (Fin n) R) ∧
      matrixUpperGap 0 (ρ a⁻¹⁻¹ : Matrix (Fin n) (Fin n) R)
    simpa only [inv_inv] using ha.symm

universe u v
variable {K : Type u} [Field K] [IsAlgClosed K] {ι : Type v}
  (H : CommHopfAlgCat.{u} K) (D : ι → CommHopfAlgCat.{u} K)
  [∀ i, Algebra.FiniteType K (D i)] [∀ i, IsReduced (D i)]
  (f : ∀ i, H ⟶ D i)

omit [IsAlgClosed K] [∀ i, Algebra.FiniteType K (D i)] [∀ i, IsReduced (D i)] in
/-- For these parameters,

```lean
Group.IsSolvable (connectedGeneratedPointSubgroup H D f)
```
-/
theorem ConnectedGeneratedPointSubgroup.isSolvable_of_triangular
    (ρ : WithConv (H →ₐ[K] K) →* (Matrix (Fin n) (Fin n) R)ˣ)
    (hρ : Function.Injective ρ)
    (htri : ∀ i (p : WithConv (D i →ₐ[K] K)),
      matrixUpperGap 0 (ρ (toConv (p.ofConv.comp ((f i).hom : H →ₐ[K] D i))) :
        Matrix (Fin n) (Fin n) R)) :
    Group.IsSolvable (connectedGeneratedPointSubgroup H D f) := by
  have hle : connectedGeneratedPointSubgroup H D f ≤ triangularRepresentationSubgroup ρ := by
    rw [connectedGeneratedPointSubgroup, Subgroup.closure_le]
    intro g hg
    obtain ⟨i, p, rfl⟩ := Set.mem_iUnion.mp hg
    constructor
    · exact htri i p
    · have hi := htri i p⁻¹
      let a := TauCeti.AlgHom.mapDomain (A := K) (f i).hom
      change matrixUpperGap 0 (ρ (a p⁻¹) : Matrix (Fin n) (Fin n) R) at hi
      rw [map_inv] at hi
      exact hi
  let ρS := ρ.comp (connectedGeneratedPointSubgroup H D f).subtype
  apply isSolvable_of_faithful_upperTriangular ρS
  · exact hρ.comp Subtype.val_injective
  · intro g
    exact (hle g.property).1

/-- For these parameters,

```lean
TauCeti.HopfIdeal.IsBorelCandidate K
      ⟨H, (TauCeti.finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal f)
```
-/
theorem CommonKernelQuotient.borelCandidate_of_triangular
    [Algebra.FiniteType K H] [∀ i, ConnectedSpace (PrimeSpectrum (D i))]
    (ρ : WithConv (H →ₐ[K] K) →* (Matrix (Fin n) (Fin n) R)ˣ)
    (hρ : Function.Injective ρ)
    (htri : ∀ i (p : WithConv (D i →ₐ[K] K)),
      matrixUpperGap 0 (ρ (toConv (p.ofConv.comp ((f i).hom : H →ₐ[K] D i))) :
        Matrix (Fin n) (Fin n) R)) :
    TauCeti.HopfIdeal.IsBorelCandidate K
      ⟨H, (TauCeti.finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal f) := by
  let := ConnectedGeneratedPointSubgroup.isSolvable_of_triangular H D f ρ hρ htri
  exact commonKernelQuotient_borelCandidate H D f

end ReductiveGroups
