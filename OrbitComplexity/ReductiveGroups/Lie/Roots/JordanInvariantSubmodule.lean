import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Jordan Invariant Submodule

Invariant subspaces are preserved by both commuting Jordan parts.
The locally finite version applies to an infinite coordinate algebra by
restricting to finite-dimensional subspaces. -/

noncomputable section
namespace ReductiveGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For these parameters,

```lean
P ∈ g.invtSubmodule
```
-/
theorem invariantSubmodule_of_mem_adjoin
    {f g : Module.End K V} {P : Submodule K V}
    (hP : P ∈ f.invtSubmodule) (hg : g ∈ Algebra.adjoin K {f}) :
    P ∈ g.invtSubmodule := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    have hx' : x = f := Set.mem_singleton_iff.mp hx
    simpa only [hx'] using hP
  | algebraMap r =>
    intro v hv
    change r • v ∈ P
    exact P.smul_mem r hv
  | add x y _ _ hx hy =>
    intro v hv
    exact P.add_mem (hx hv) (hy hv)
  | mul x y _ _ hx hy =>
    intro v hv
    exact hx (hy hv)

/-- Uniqueness identifies any given commuting Jordan decomposition with the
polynomial decomposition, so its parts preserve every invariant subspace. -/
theorem invariantSubmodule_jordanParts [FiniteDimensional K V] [PerfectField K]
    {f n s : Module.End K V} (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hc : Commute n s) (h : f = n + s)
    {P : Submodule K V} (hP : P ∈ f.invtSubmodule) :
    P ∈ n.invtSubmodule ∧ P ∈ s.invtSubmodule := by
  obtain ⟨n', hn', s', hs', hn'nil, hs'ss, heq⟩ :=
    f.exists_isNilpotent_isSemisimple
  have hcs : Commute f s' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs' (Commute.refl f)
  have hcn : Commute n' s' :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hn' hcs.symm).symm
  obtain ⟨en, es⟩ := Module.End.isNilpotent_isSemisimple_unique
    hn hs hn'nil hs'ss hc hcn (h.symm.trans heq)
  rw [en, es]
  exact ⟨invariantSubmodule_of_mem_adjoin hP hn',
    invariantSubmodule_of_mem_adjoin hP hs'⟩

/-- A finite invariant subspace containing a vector is enough to transfer
invariance of another subspace to each Jordan part at that vector. -/
theorem invariantSubmodule_jordanParts_at [PerfectField K]
    {f n s : Module.End K V} (hc : Commute n s) (h : f = n + s)
    {P W : Submodule K V} [FiniteDimensional K W]
    (hP : P ∈ f.invtSubmodule)
    (hnW : W ∈ n.invtSubmodule) (hsW : W ∈ s.invtSubmodule)
    (hn : IsNilpotent (n.restrict hnW))
    (hs : Module.End.IsSemisimple (s.restrict hsW))
    {v : V} (hvP : v ∈ P) (hvW : v ∈ W) :
    n v ∈ P ∧ s v ∈ P := by
  have hfW : W ∈ f.invtSubmodule := by
    intro x hx
    change f x ∈ W
    rw [h, LinearMap.add_apply]
    exact W.add_mem (hnW hx) (hsW hx)
  have hrestrict : f.restrict hfW = n.restrict hnW + s.restrict hsW := by
    ext x
    exact DFunLike.congr_fun h (x : V)
  have hcommute : Commute (n.restrict hnW) (s.restrict hsW) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun hc.eq (x : V)
  have hPW : P.comap W.subtype ∈ Module.End.invtSubmodule (f.restrict hfW) := by
    intro x hx
    exact hP hx
  obtain ⟨hPn, hPs⟩ := invariantSubmodule_jordanParts hn hs hcommute hrestrict hPW
  exact ⟨hPn (show (⟨v, hvW⟩ : W) ∈ P.comap W.subtype from hvP),
    hPs (show (⟨v, hvW⟩ : W) ∈ P.comap W.subtype from hvP)⟩

end ReductiveGroups
