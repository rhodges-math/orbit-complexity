import OrbitComplexity.FrobeniusSplitting.Modules.RelativeScalars
import OrbitComplexity.FrobeniusSplitting.Modules.SplitEqualizer

/-! # Character functions determined by the identity section -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable (S : Scheme.{u})

private theorem pull_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (f ≫ g) =
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S g ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f := by
  change (FrobeniusSplitting.CharacterLine.relativeFunctions S).map ((f ≫ g).op) =
    (FrobeniusSplitting.CharacterLine.relativeFunctions S).map g.op ≫
        (FrobeniusSplitting.CharacterLine.relativeFunctions S).map f.op
  rw [op_comp, Functor.map_comp]

private theorem pull_id (X : Over S) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (𝟙 X) = 𝟙
        (FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X) := by
  exact (FrobeniusSplitting.CharacterLine.relativeFunctions S).map_id (op X)

/-- Inserting the group identity trivializes regular functions with a fixed character. -/
def identityCharacterIso {A X Q : Over S} (m f : Q ⟶ X) (i : X ⟶ Q)
    (p : X ⟶ A) (s : A ⟶ X) (c : Γ(X.left, ⊤)) (v : Γ(Q.left, ⊤))
    (him : i ≫ m = 𝟙 X) (hif : i ≫ f = p ≫ s) (hsp : s ≫ p = 𝟙 A)
    (hbase : m ≫ p = f ≫ p) (hvi : i.left.appTop v = c)
    (hcs : s.left.appTop c = 1)
    (hcm : m.left.appTop c = f.left.appTop c * v) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsObj S A ≅
      equalizer (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S m)
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v) := by
  apply FrobeniusSplitting.CharacterLine.splitEqualizerIso
      (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S m)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S i)
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S s)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c)
  · rw [← FrobeniusSplitting.CharacterLine.pull_comp, him, FrobeniusSplitting.CharacterLine.pull_id]
  · calc
      (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsMap S i =
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsMap S i ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c := by
            rw [Category.assoc, FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul, hvi]
      _ = FrobeniusSplitting.CharacterLine.relativeFunctionsMap S s ≫
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
              FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c) := by
            rw [← Category.assoc, ← FrobeniusSplitting.CharacterLine.pull_comp, hif,
                FrobeniusSplitting.CharacterLine.pull_comp, Category.assoc]
  · calc
      (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsMap S s =
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsMap S s ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S A 1 := by
            rw [Category.assoc, FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul, hcs]
      _ = 𝟙 _ := by
        rw [← Category.assoc, ← FrobeniusSplitting.CharacterLine.pull_comp, hsp,
            FrobeniusSplitting.CharacterLine.pull_id,
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul_one, Category.id_comp]
  · calc
      (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsMap S m =
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (m ≫ p) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q (m.left.appTop c) := by
            rw [Category.assoc, FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul, ←
                Category.assoc, ← FrobeniusSplitting.CharacterLine.pull_comp]
      _ = FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (f ≫ p) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q (v * f.left.appTop c) := by
            rw [hbase, hcm, mul_comm (f.left.appTop c) v]
      _ = (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c) ≫
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
              FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v) := by
            rw [FrobeniusSplitting.CharacterLine.pull_comp,
                FrobeniusSplitting.CharacterLine.relativeFunctionsSmul_mul]
            have hnat : FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c ≫
                FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f =
                FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
                    FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q (f.left.appTop c) :=
              FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul S f c
            simpa only [Category.assoc] using
              congrArg (fun t => FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫ t ≫
                FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v) hnat.symm

end FrobeniusSplitting.CharacterLine
