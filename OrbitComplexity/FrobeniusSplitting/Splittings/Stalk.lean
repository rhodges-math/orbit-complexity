import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme

/-!
# Frobenius splittings on stalks

A splitting of the structure sheaf induces a splitting on each stalk. Taking
the germ of a section commutes with these splittings.

## Main definitions

* `FrobeniusSplitting.SchemeSplitting.onStalk`: the induced splitting on a stalk.

## Main results

* `FrobeniusSplitting.SchemeSplitting.onStalk_germ`: compatibility with germs.

## Implementation notes

The map on a stalk is constructed from the colimit of the local section maps.
Addition and multiplication are checked over a common open neighborhood.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

variable {X : Scheme} {p : ℕ}

private def stalkCocone (splitting : SchemeSplitting X p) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf ⋙ forget CommRingCat) where
  pt := X.presheaf.stalk x
  ι :=
    { app := fun U ↦ TypeCat.ofHom fun a ↦
        X.presheaf.germ U.unop.1 x U.unop.2 (splitting.onOpen U.unop.1 a)
      naturality := by
        intro U V f
        obtain ⟨⟨U, hU⟩⟩ := U
        obtain ⟨⟨V, hV⟩⟩ := V
        have hVU : V ≤ U := f.unop.le
        ext a
        change X.presheaf.germ V x hV
          (splitting.onOpen V (X.presheaf.map (homOfLE hVU).op a)) =
            X.presheaf.germ U x hU (splitting.onOpen U a)
        exact (congrArg (X.presheaf.germ V x hV)
          (splitting.restrict_comm (U := U) (V := V) hVU a)).trans
            (X.presheaf.germ_res_apply (homOfLE hVU) x hV (splitting.onOpen U a)) }

private def stalkMap (splitting : SchemeSplitting X p) (x : X) :
    X.presheaf.stalk x → X.presheaf.stalk x :=
  (isColimitOfPreserves (forget CommRingCat)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))).desc
      (stalkCocone splitting x)

private theorem stalkMap_germ (splitting : SchemeSplitting X p) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    stalkMap splitting x (X.presheaf.germ U x hx a) =
      X.presheaf.germ U x hx (splitting.onOpen U a) := by
  exact CategoryTheory.types_congr_hom ((isColimitOfPreserves (forget CommRingCat)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))).fac
      (stalkCocone splitting x) (op ⟨U, hx⟩)) a

private theorem stalk_induction_on₂ (x : X) (a b : X.presheaf.stalk x)
    {property : X.presheaf.stalk x → X.presheaf.stalk x → Prop}
    (hsections : ∀ (U : X.Opens) (hx : x ∈ U) (s t : Γ(X, U)),
      property (X.presheaf.germ U x hx s) (X.presheaf.germ U x hx t)) : property a b := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, t, rfl⟩ := X.presheaf.exists_le_germ_eq b hxU
  simpa only [X.presheaf.germ_res_apply] using
    hsections V hxV (X.presheaf.map (homOfLE hVU).op s) t

/-- A scheme splitting induces a splitting of each stalk of the structure sheaf. -/
def onStalk (splitting : SchemeSplitting X p) (x : X) :
    RingSplitting (X.presheaf.stalk x) p where
  toAddMonoidHom :=
    { toFun := stalkMap splitting x
      map_zero' := by
        simpa only [map_zero, RingSplitting.map_zero] using
          stalkMap_germ splitting x ⊤ (by trivial) 0
      map_add' a b := by
        refine stalk_induction_on₂ x a b (property := fun a b ↦
          stalkMap splitting x (a + b) = stalkMap splitting x a + stalkMap splitting x b) ?_
        intro U hx s t
        rw [← (X.presheaf.germ U x hx).hom.map_add, stalkMap_germ,
          (splitting.onOpen U).map_add, (X.presheaf.germ U x hx).hom.map_add,
          stalkMap_germ, stalkMap_germ] }
  map_pow_mul' a b := by
    change stalkMap splitting x (a ^ p * b) = a * stalkMap splitting x b
    refine stalk_induction_on₂ x a b (property := fun a b ↦
      stalkMap splitting x (a ^ p * b) = a * stalkMap splitting x b) ?_
    intro U hx s t
    rw [← (X.presheaf.germ U x hx).hom.map_pow,
      ← (X.presheaf.germ U x hx).hom.map_mul, stalkMap_germ,
      (splitting.onOpen U).map_pow_mul, (X.presheaf.germ U x hx).hom.map_mul,
      stalkMap_germ]
  map_one' := by
    change stalkMap splitting x 1 = 1
    simpa only [map_one, RingSplitting.map_one] using
      stalkMap_germ splitting x ⊤ (by trivial) 1

end

end FrobeniusSplitting.SchemeSplitting
