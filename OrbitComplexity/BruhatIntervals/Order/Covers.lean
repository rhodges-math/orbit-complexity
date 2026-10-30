import OrbitComplexity.BruhatIntervals.Graph.LongEdges
import OrbitComplexity.BruhatIntervals.Order.Interval
import Mathlib.Order.Cover
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Covers in Bruhat order

An intrinsic Bruhat-order cover is a reflection edge of unit Coxeter length. Every longer edge
has an intermediate vertex, by its directed three-edge refinement.

## Main results

* `bruhat_covBy_step`: every Bruhat-order cover is a directed reflection edge.
* `bruhat_covBy_iff`: a comparison is a cover exactly when its length gap is one.
* `exists_le_bruhat_covBy`: every proper interval has a cover immediately below its top.
* `exists_bruhat_covBy_le`: every proper interval has a cover immediately above its bottom.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.1 and 2.2.
* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  proof of Proposition 3.3, claim (i).
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- Every intrinsic Bruhat-order cover is a directed reflection edge. -/
theorem bruhat_covBy_step {u v : W} :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ v → cs.BruhatStep u v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hcover
  have hle : cs.BruhatLE u v := hcover.le
  rcases Relation.ReflTransGen.cases_head hle with heq | ⟨w, hstep, hwv⟩
  · exact (hcover.lt.ne heq).elim
  · rcases hcover.eq_or_eq hstep.bruhatLE hwv with hwu | hwv
    · have hlt := hstep.length_lt
      rw [hwu] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · rwa [hwv] at hstep

/-- A Bruhat comparison is an intrinsic cover exactly when its Coxeter length gap is one. -/
theorem bruhat_covBy_iff (u v : W) :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ v ↔ cs.BruhatLE u v ∧ cs.length v = cs.length u + 1 := by
  let : PartialOrder W := cs.bruhatPartialOrder
  constructor
  · intro hcover
    refine ⟨hcover.le, ?_⟩
    have hstep := bruhat_covBy_step cs hcover
    have hlt := hstep.length_lt
    by_contra hne
    obtain ⟨a, b, hfirst, hmiddle, hlast, _⟩ := long_edge_path cs u v hstep (by omega)
    rcases hcover.eq_or_eq hfirst.bruhatLE (hmiddle.bruhatLE.trans hlast.bruhatLE) with
      hau | hav
    · have hlength := hfirst.length_lt
      rw [hau] at hlength
      exact Nat.lt_irrefl _ hlength
    · have hlength := hmiddle.length_lt.trans hlast.length_lt
      rw [hav] at hlength
      exact Nat.lt_irrefl _ hlength
  · rintro ⟨hle, hlength⟩
    refine ⟨lt_of_le_of_ne hle ?_, ?_⟩
    · intro heq
      rw [heq] at hlength
      omega
    · intro w hlow hhigh
      have hfirst := (show cs.BruhatLE u w from hlow.le).length_lt_of_ne hlow.ne
      have hsecond := (show cs.BruhatLE w v from hhigh.le).length_lt_of_ne hhigh.ne
      omega

/-- Every proper Bruhat interval contains a cover immediately below its top endpoint. -/
theorem exists_le_bruhat_covBy {u v : W} (hle : cs.BruhatLE u v) (hne : u ≠ v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ∃ z : W, cs.BruhatLE u z ∧ z ⋖ v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  let candidates : Set W := {z | cs.BruhatLE u z ∧ z < v}
  have hfinite : candidates.Finite := (bruhatInterval_finite cs u v).subset
    (fun _ hz => ⟨hz.1, hz.2.le⟩)
  have hnonempty : candidates.Nonempty :=
    ⟨u, Relation.ReflTransGen.refl, lt_of_le_of_ne hle hne⟩
  obtain ⟨z, hz, hmax⟩ := Set.exists_max_image candidates cs.length hfinite hnonempty
  refine ⟨z, hz.1, hz.2, ?_⟩
  intro w hzw hwv
  have hcandidate : w ∈ candidates := ⟨hz.1.trans hzw.le, hwv⟩
  have hlength := hmax w hcandidate
  have hstrict := (show cs.BruhatLE z w from hzw.le).length_lt_of_ne hzw.ne
  omega

/-- Every proper Bruhat interval contains a cover immediately above its bottom endpoint. -/
theorem exists_bruhat_covBy_le {u v : W} (hle : cs.BruhatLE u v) (hne : u ≠ v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ∃ z : W, u ⋖ z ∧ cs.BruhatLE z v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  let candidates : Set W := {z | u < z ∧ cs.BruhatLE z v}
  have hfinite : candidates.Finite := (bruhatInterval_finite cs u v).subset
    (fun _ hz => ⟨hz.1.le, hz.2⟩)
  have hnonempty : candidates.Nonempty :=
    ⟨v, lt_of_le_of_ne hle hne, Relation.ReflTransGen.refl⟩
  obtain ⟨z, hz, hmin⟩ := Set.exists_min_image candidates cs.length hfinite hnonempty
  refine ⟨z, ⟨hz.1, ?_⟩, hz.2⟩
  intro w huw hwz
  have hcandidate : w ∈ candidates := ⟨huw, hwz.le.trans hz.2⟩
  have hlength := hmin w hcandidate
  have hstrict := (show cs.BruhatLE w z from hwz.le).length_lt_of_ne hwz.ne
  omega

end BruhatIntervals
