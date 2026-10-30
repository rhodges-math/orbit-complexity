import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Multiplication and relabelling of root product coordinates

Relabelling roots renames polynomial variables. Concatenating two root orders
computes the group multiplication pullback into the tensor product of their charts.
-/

set_option maxHeartbeats 400000

noncomputable section
namespace ReductiveGroups
open TauCeti
open scoped TensorProduct
universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  {ι κ : Type u}

/-- Relabelling an ordered root product relabels its polynomial coordinates. -/
theorem gaProductCoordinate_map (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (f : ι → κ) (l : List ι) :
    gaProductCoordinate x (l.map f) =
      (MvPolynomial.rename f).comp (gaProductCoordinate (fun i => x (f i)) l) := by
  have h := gaProductCoordinate_eval (fun i => x (f i)) l
    (fun i => (MvPolynomial.X (f i) : MvPolynomial κ K))
  have he : MvPolynomial.aeval (fun i => (MvPolynomial.X (f i) : MvPolynomial κ K)) =
      (MvPolynomial.rename f : MvPolynomial ι K →ₐ[K] MvPolynomial κ K) := by
    ext i
    simp
  rw [he] at h
  simpa only [gaProductCoordinate, List.map_map, Function.comp_def] using h.symm

/-- Concatenated root products pull back multiplication into the tensor product of charts. -/
theorem gaProductCoordinate_sum (x : ι ⊕ κ → B →ₐc[K] SymmetricAlgebra K K)
    (l : List ι) (m : List κ) :
    gaProductCoordinate x (l.map Sum.inl ++ m.map Sum.inr) =
      (MvPolynomial.tensorEquivSum K ι κ K).toAlgHom.comp
        ((Algebra.TensorProduct.map (gaProductCoordinate (fun i => x (.inl i)) l)
          (gaProductCoordinate (fun j => x (.inr j)) m)).comp (Bialgebra.comulAlgHom K B)) := by
  let f := gaProductCoordinate (fun i => x (.inl i)) l
  let g := gaProductCoordinate (fun j => x (.inr j)) m
  let E := MvPolynomial.tensorEquivSum K ι κ K
  let φ : B ⊗[K] B →ₐ[K] MvPolynomial (ι ⊕ κ) K :=
    E.toAlgHom.comp (Algebra.TensorProduct.map f g)
  have hleft : φ.comp Algebra.TensorProduct.includeLeft =
      (MvPolynomial.rename Sum.inl).comp f := by
    apply AlgHom.ext
    intro b
    change E ((Algebra.TensorProduct.map f g) (b ⊗ₜ[K] 1)) =
      MvPolynomial.rename Sum.inl (f b)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    generalize f b = p
    induction p using MvPolynomial.induction_on with
    | C a => simp [E]
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
    | mul_X p i hp =>
      rw [show (p * MvPolynomial.X i) ⊗ₜ[K] (1 : MvPolynomial κ K) =
        (p ⊗ₜ[K] 1) * (MvPolynomial.X i ⊗ₜ[K] 1) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, hp]
      simp [E]
  have hright : φ.comp Algebra.TensorProduct.includeRight =
      (MvPolynomial.rename Sum.inr).comp g := by
    apply AlgHom.ext
    intro b
    change E ((Algebra.TensorProduct.map f g) (1 ⊗ₜ[K] b)) =
      MvPolynomial.rename Sum.inr (g b)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    generalize g b = p
    induction p using MvPolynomial.induction_on with
    | C a => simp [E]
    | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [show (1 : MvPolynomial ι K) ⊗ₜ[K] (p * MvPolynomial.X i) =
        (1 ⊗ₜ[K] p) * (1 ⊗ₜ[K] MvPolynomial.X i) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, hp]
      simp [E]
  have h := TauCeti.Bialgebra.toConv_comp_comulAlgHom φ
  simp only [TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom,
    TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom] at h
  change WithConv.toConv (φ.comp (Bialgebra.comulAlgHom K B)) =
    WithConv.toConv (φ.comp Algebra.TensorProduct.includeLeft) *
      WithConv.toConv (φ.comp Algebra.TensorProduct.includeRight) at h
  rw [hleft, hright, ← gaProductCoordinate_map, ← gaProductCoordinate_map] at h
  have hprod : WithConv.toConv (gaProductCoordinate x (l.map Sum.inl ++ m.map Sum.inr)) =
      WithConv.toConv (gaProductCoordinate x (l.map Sum.inl)) *
        WithConv.toConv (gaProductCoordinate x (m.map Sum.inr)) := by
    simp only [gaProductCoordinate, List.map_append, List.prod_append, WithConv.toConv_ofConv]
  exact (congrArg WithConv.ofConv (hprod.trans h.symm)).trans (by
    rfl)

end ReductiveGroups
