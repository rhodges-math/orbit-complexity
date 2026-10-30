import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.SubwordFaces
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BruhatSubword
import Batteries.Tactic.Lint

/-! # Reduced faces for the Bruhat interval of a word -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory

namespace SchubertGeometry

open ReductiveGroups

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- Each Weyl element below a reduced word is the product of a reduced subword
whose BSDH face is closed, preserves the flag endpoint, and has the finite sum
of the corresponding omitted-letter ideals as its scheme ideal. -/
theorem bsdh_bruhat_face (w : List G.rootBase.support)
    (hw : (weylCoxeterSystem G.rootBase).IsReduced w)
    (x : G.rootSystem.weylGroup)
    (hx : WeylBruhatLE G.rootBase x (simpleWeylWord G.rootBase w)) :
    ∃ v : List G.rootBase.support, v.Sublist w ∧
      (weylCoxeterSystem G.rootBase).IsReduced v ∧
      simpleWeylWord G.rootBase v = x ∧
      ∃ (a : bsdhScheme G v ⟶ bsdhScheme G w) (F : Finset (Fin w.length)),
        IsClosedImmersion a ∧ a ≫ bsdhMap G w = bsdhMap G v ∧
          a.ker = F.sup (fun k => (bsdhOmitMap G w k).ker) := by
  obtain ⟨v, hv, hprod, hred⟩ :=
    (weylBruhatLE_iff_subword G.rootBase x w
      ((weylCoxeterSystem_isReduced_iff G.rootBase w).mp hw)).mp hx
  obtain ⟨a, F, ha, he, hk⟩ := bsdh_subword_face G hv
  exact ⟨v, hv, (weylCoxeterSystem_isReduced_iff G.rootBase v).mpr hred,
    hprod, a, F, ha, he, hk⟩

end SchubertGeometry
