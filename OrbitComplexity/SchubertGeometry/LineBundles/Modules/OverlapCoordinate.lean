import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterRestrictions

/-! # Character coordinates of the regular rank-one Borel overlap -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev coordinate (K : Type u) [Field K] :=
  MonoidAlgebra K (Multiplicative ℤ)

private def torusOverlap (i : G.rootBase.support) :
    WithConv (G.borelAlgebra →ₐ[K] coordinate K) :=
  toConv ((((MonoidAlgebra.mapDomainBialgHom K
    (Coroot.simpleCorootCharacter G i)).comp (torusCharacterCoordinates G)).toAlgHom).comp
      (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
        G.borel_le_torus).hom.toAlgHom)

private def upperOverlap (i : G.rootBase.support) :
    WithConv (G.borelAlgebra →ₐ[K] coordinate K) :=
  gaParameterPoint (simpleBorelRootMap G i)
    (-MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1)

/-- The coordinate map of the coroot-times-upper-root Borel overlap. -/
def simpleOverlapCoordinate (i : G.rootBase.support) :
    G.borelAlgebra →ₐ[K] coordinate K :=
  (torusOverlap G i * upperOverlap G i).ofConv

omit [IsAlgClosed K] [CharZero K] in
private theorem character_mul
    {B A : Type*} [CommRing B] [HopfAlgebra K B] [CommRing A] [Algebra K A]
    (chi : coordinate K →ₐc[K] B) (a b : WithConv (B →ₐ[K] A)) :
    (a * b).ofConv (chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) =
      a.ofConv (chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) *
        b.ofConv (chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) := by
  change (AlgHom.mapDomain chi (a * b)).ofConv
    (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) = _
  rw [map_mul, MonoidAlgebra.convMul_algHom_single_one]
  rfl

private theorem torusOverlap_character (p : ℕ) (hp : Odd p) (i : G.rootBase.support) :
    (torusOverlap G i).ofConv (borelCharacterMap G (G.oddRootCharacter p)
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) =
      MonoidAlgebra.single (Multiplicative.ofAdd ((p - 1 : ℕ) : ℤ)) 1 := by
  change (MonoidAlgebra.mapDomainBialgHom K (Coroot.simpleCorootCharacter G i))
    (torusCharacterCoordinates G
      ((CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj G.borel_le_torus).hom
        (borelCharacterMap G (G.oddRootCharacter p)
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))) = _
  have hr := congrArg
    (fun f : coordinate K →ₐc[K] G.torusAlgebra =>
      f (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))
    (borelCharacterMap_restrict G (G.oddRootCharacter p))
  change (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj G.borel_le_torus).hom
    (borelCharacterMap G (G.oddRootCharacter p)
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = _ at hr
  rw [hr]
  exact torusCharacter_coroot_generator G p hp i

private theorem upperOverlap_character (i : G.rootBase.support) (chi : G.characters) :
    (upperOverlap G i).ofConv (borelCharacterMap G chi
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = 1 := by
  change ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := coordinate K)).symm
    (Multiplicative.ofAdd (-MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1))).ofConv
      (((simpleBorelRootMap G i).comp (borelCharacterMap G chi))
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = 1
  rw [borelCharacter_upper_generator]
  exact map_one _

/-- The same Borel character gives the Laurent monomial of degree p minus one. -/
theorem simpleOverlapCoordinate_character (p : ℕ) (hp : Odd p)
    (i : G.rootBase.support) :
    simpleOverlapCoordinate G i (borelCharacterMap G (G.oddRootCharacter p)
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) =
      MonoidAlgebra.single (Multiplicative.ofAdd ((p - 1 : ℕ) : ℤ)) 1 := by
  rw [simpleOverlapCoordinate, character_mul, torusOverlap_character G p hp,
    upperOverlap_character, mul_one]

end SchubertGeometry.ProjectiveLine
