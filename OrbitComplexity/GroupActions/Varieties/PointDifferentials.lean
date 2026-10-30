import OrbitComplexity.GroupActions.Varieties.PointDerivations

/-! # Differential criteria in point coordinates

The coefficient synonym for point derivations agrees with an existing algebra tower.
Consequently surjective or bijective precomposition of point derivations detects smoothness
or etaleness through the residue-field criteria.

## Main results

* `GroupActions.smooth_of_surjective_pointDerivations`: point derivations detect smoothness.
* `GroupActions.etale_of_bijective_pointDerivations`: point derivations detect etaleness.
-/

namespace GroupActions

noncomputable section

universe u v w x

section Towers

variable (R : Type u) (A : Type v) (B : Type w) (C : Type x)
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A B C]

/-- Surjectivity of point precomposition agrees with surjectivity for tower derivations. -/
theorem surjective_pointPrecomp_iff :
    Function.Surjective (pointDerivationPrecomp (IsScalarTower.toAlgHom R A B)
      (IsScalarTower.toAlgHom R B C)) ↔
    Function.Surjective (fun d : Derivation R B C => d.compAlgebraMap A) := by
  let e := pointDerivationOfTower R B C
  let E := (pointDerivationCongr (pointOfTower_comp R A B C)).trans
    (pointDerivationOfTower R A C)
  let P := pointDerivationPrecomp (IsScalarTower.toAlgHom R A B)
    (IsScalarTower.toAlgHom R B C)
  let D := fun d : Derivation R B C => d.compAlgebraMap A
  have hfun : E ∘ P = D ∘ e := funext fun d => pointDerivationOfTower_comp R A B C d
  calc
    Function.Surjective P ↔ Function.Surjective (E ∘ P) :=
      (EquivLike.comp_surjective P E).symm
    _ ↔ Function.Surjective (D ∘ e) := by rw [hfun]
    _ ↔ Function.Surjective D := EquivLike.surjective_comp e D

/-- Bijectivity of point precomposition agrees with bijectivity for tower derivations. -/
theorem bijective_pointPrecomp_iff :
    Function.Bijective (pointDerivationPrecomp (IsScalarTower.toAlgHom R A B)
      (IsScalarTower.toAlgHom R B C)) ↔
    Function.Bijective (fun d : Derivation R B C => d.compAlgebraMap A) := by
  let e := pointDerivationOfTower R B C
  let E := (pointDerivationCongr (pointOfTower_comp R A B C)).trans
    (pointDerivationOfTower R A C)
  let P := pointDerivationPrecomp (IsScalarTower.toAlgHom R A B)
    (IsScalarTower.toAlgHom R B C)
  let D := fun d : Derivation R B C => d.compAlgebraMap A
  have hfun : E ∘ P = D ∘ e := funext fun d => pointDerivationOfTower_comp R A B C d
  calc
    Function.Bijective P ↔ Function.Bijective (E ∘ P) :=
      (EquivLike.comp_bijective P E).symm
    _ ↔ Function.Bijective (D ∘ e) := by rw [hfun]
    _ ↔ Function.Bijective D := EquivLike.bijective_comp e D

end Towers

section Algebras

variable (R : Type u) (S : Type v) (T : Type w)
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Surjective point-derivation maps on every maximal residue field detect smoothness. -/
theorem smooth_of_surjective_pointDerivations [Algebra.Smooth R S] [Algebra.Smooth R T]
    [Algebra.FinitePresentation S T]
    (hmap : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Surjective
      (pointDerivationPrecomp (IsScalarTower.toAlgHom R S T)
        (IsScalarTower.toAlgHom R T (IsLocalRing.ResidueField (Localization.AtPrime ideal))))) :
    Algebra.Smooth S T := by
  apply smooth_of_surjective_derivations R S T
  intro ideal hmaximal
  exact (surjective_pointPrecomp_iff R S T
    (IsLocalRing.ResidueField (Localization.AtPrime ideal))).mp (hmap ideal)

/-- Bijective point-derivation maps on every maximal residue field detect etaleness. -/
theorem etale_of_bijective_pointDerivations [Algebra.Smooth R S] [Algebra.Smooth R T]
    [Algebra.FinitePresentation S T]
    (hmap : ∀ (ideal : Ideal T) [ideal.IsMaximal], Function.Bijective
      (pointDerivationPrecomp (IsScalarTower.toAlgHom R S T)
        (IsScalarTower.toAlgHom R T (IsLocalRing.ResidueField (Localization.AtPrime ideal))))) :
    Algebra.Etale S T := by
  apply etale_of_bijective_derivations R S T
  intro ideal hmaximal
  exact (bijective_pointPrecomp_iff R S T
    (IsLocalRing.ResidueField (Localization.AtPrime ideal))).mp (hmap ideal)

end Algebras

end

end GroupActions
