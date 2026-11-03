# Lean verification of *Orbit structures and complexity in Schubert and Richardson Varieties*

This repository, `rhodges-math/orbit-complexity` (release 1.0.0), contains a
Lean 4 formalization of *Orbit structures and complexity in Schubert and
Richardson Varieties* (Yibo Gao and Reuven Hodges, 2024),
[arXiv:2405.13774](https://arxiv.org/abs/2405.13774).

All results of the paper are formalized. Let $G$ be a connected reductive group
with a maximal torus $T$ contained in a Borel subgroup $B$, and Weyl group $W$.
For $u\le v$ in $W$, the $T$-complexity of the Richardson variety
$\mathcal{R}\_{u,v}$ is $\ell(v)-\ell(u)-\mathrm{ad}(u,v)$, where the algebraic
dimension $\mathrm{ad}(u,v)=\dim\mathrm{AD}(u,v)$ of the Bruhat interval
$\[u,v\]$ is the dimension of the span $\mathrm{AD}(u,v)$ of the root labels of
its Bruhat graph; moreover, $\mathrm{ad}(u,v)$ is the largest value of
$\ell(v)-\ell(w)$ for which $\mathcal{R}\_{w,v}$ is toric
(Theorem 1.2). In particular the $T$-complexity of the Schubert variety $X\_w$ is
$\ell(w)-\mathrm{supp}(w)$ (Corollary 1.3). On each Deodhar component of an open
Richardson variety, the dimension of the torus orbit of a point is the
dimension of the span of the roots $\beta\_k$ of its nonzero coordinates, and at
a general point it is the dimension of the space
$\mathrm{TD}(\mathbf{u},\mathbf{v})$ attached to the distinguished subword,
which is contained in $\mathrm{AD}(u,v)$, with equality for the positive
distinguished subword (Theorem 1.4). For a set $I$ of simple roots
and the left parabolic decomposition $w={}\_Iw\\,{}^Iw$, translation by ${}\_Iw$
maps the torus orbits of the Schubert cell $X^\circ\_{{}^Iw}$ onto the
Levi-Borel orbits of $X^\circ\_w$, bijectively and preserving codimension when
the Levi subgroup $L\_I$ acts on $X\_w$ (Theorem 1.5), and the $L\_I$-complexity of
$X\_w$ is then $\ell({}^Iw)-\mathrm{supp}({}^Iw)$ (Theorem 1.6). These
complexities carry over to Schubert varieties in partial flag varieties, which
gives a classification of the toric ones (Theorem 4.11 and Corollary 4.12). The
results that the paper cites are proved as well, among them the normality of
Schubert and Richardson varieties, the moment-map description of Bruhat
interval polytopes of Tsukerman and Williams, Deodhar's decomposition, Brion's
orbit dimension formula, and the invariance of complexity under equivariant
birational maps, through Rosenlicht's theorem. Every other statement of the
paper is formalized too: its definitions, lemmas, propositions, examples,
remarks, the displayed equations its proofs use, and the claims made in its
prose, 74 entries in all, listed in [docs/STATEMENTS.md](docs/STATEMENTS.md).

These results are proved with no hypotheses beyond Lean's standard axioms. The
development uses Lean **4.35.0-rc3**, a pinned version of **Mathlib**, and the
**Tau Ceti** library. Lean 4.35.0-rc3 is a release candidate; the pin may move
to the stable Lean 4.35.0 release.

Its six general libraries are independent of the paper and may be of use beyond
it, since they prove in general form several standard results that other
projects can import without the paper: the normality of Schubert varieties in
$G/B$ and in every partial flag variety $G/P\_J$ and of Richardson varieties, by
Frobenius splitting; Deodhar's decomposition of open Richardson varieties;
Brion's formula for the dimension of an orbit, Rosenlicht's theorem and the
invariance of complexity under equivariant birational maps; and the results of
Tsukerman and Williams relating torus orbit closures, moment maps and Bruhat
interval polytopes; together with their foundations, from the Bruhat
decomposition, reductive groups, Coxeter groups and Bruhat intervals to flag
varieties and Bott–Samelson resolutions; see [Libraries](#libraries).

## AI assistance and verification

**I used GPT-6.1 Sol and Claude Opus 5.5 to help construct the Lean files.** I
reviewed all definitions, hypotheses, and theorem statements to check that
they faithfully express the intended mathematics, including the results of
the paper listed below.

The development was compiled with Lean, and the axiom dependencies of every
declaration were audited: they use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry`-based proofs or additional unproved axioms.
The mathematical review addresses the correspondence between the formal
statements and the paper, which Lean's proof checking alone does not establish.

## Main results

The entry point is
[OrbitComplexity/Paper/Main.lean](OrbitComplexity/Paper/Main.lean), which
imports every result of the paper; [docs/STATEMENTS.md](docs/STATEMENTS.md)
lists each statement of the paper with its Lean counterparts.

```lean
import OrbitComplexity.Paper.Main

open ReductiveGroups BruhatIntervals GroupActions SchubertGeometry SchubertOrbits

#check richardson_complexity_formula
#check schubert_complexity_formula
#check deodharComponent_weights
#check torus_levi_orbits
#check levi_complexity_properties
#check partial_schubert_levi
#check partial_schubert_toric
```

Names below are relative to the namespace `SchubertOrbits` of the paper or to
the namespaces `ReductiveGroups`, `BruhatIntervals`, `GroupActions` and
`SchubertGeometry` of the general libraries, all opened above. The length and
Bruhat order of a Coxeter system are `CoxeterSystem.length` (Mathlib) and
`CoxeterSystem.BruhatLE` (Tau Ceti).

### Notation

The paper works over $\mathbb{C}$. The formalization works over an arbitrary
algebraically closed field $K$ of characteristic zero, and the declarations
ending in `_complex` state the results over $\mathbb{C}$. A variety is a reduced
separated scheme of finite type over $K$ (`Variety K`), with its set of
$K$-points. An algebraic group acts on a variety by a morphism of schemes;
orbits are the orbits of its $K$-points on the $K$-points of the variety, and
the dimension of an orbit is the dimension of its closure. The Weyl group is
that of the root system of $(G,T)$, identified with $N\_G(T)/T$ by
`weylQuotientEquiv`, and `G.weylPoint w` is a fixed representative of $w$ in
$N\_G(T)$. The flag, Schubert, Richardson and partial flag varieties are schemes:
$G/B$ is smooth and proper over $K$, its $K$-points are the cosets $gB$, and
$X\_w$ and $\mathcal{R}\_{u,v}$ are its reduced closed subschemes on the closures
of $BwB/B$ and on $X\_v\cap X^u$.

| Paper | Lean |
| --- | --- |
| $G$ over $K$, with $T\subseteq B\subseteq G$ | `G : ReductiveGroupData K` |
| $W$; the simple roots $\Delta$; $I\subseteq\Delta$ | `G.weylGroup`; `G.rootBase.support`; `I : Set G.rootBase.support` |
| $\ell(w)$; $u\le v$; $\[u,v\]$ | `(weylCoxeterSystem G.rootBase).length w`; `(weylCoxeterSystem G.rootBase).BruhatLE u v`; `bruhatInterval (weylCoxeterSystem G.rootBase) u v` |
| $\mathrm{supp}(w)$; $\mathcal{D}\_L(w)$ | `supportCard (weylCoxeterSystem G.rootBase) w`; `leftDescents (weylCoxeterSystem G.rootBase) w` |
| $w={}\_Iw\\,{}^Iw$ | `leftParabolicFactor G.rootBase I w`, `leftParabolicRepresentative G.rootBase I w` |
| $\mathrm{AD}(u,v)$; $\mathrm{ad}(u,v)$ | `labelSpan (weylRealization G.rootBase) u v`; `algebraicDim (weylRealization G.rootBase) u v` |
| $G/B$ | `flagVariety G` |
| $X^\circ\_w$; $X\_w$; $X^w$ | `schubertCell G w`; `schubertVariety G w`; `oppositeSchubertVariety G w` |
| $\mathcal{R}\_{u,v}=X\_v\cap X^u$ | `richardsonVariety G u v` |
| $T$, $L\_I$, $B\_{L\_I}=L\_I\cap B$ acting on varieties | `torusVariety G`, `leviVariety G I`, `leviBorelVariety G I` |
| $L\_I$ as a reductive group with Borel subgroup $B\_{L\_I}$ | `leviGroupData G I` |
| $\dim Hx$; $\dim X-\dim Hx$ | `orbitNatDim H X x`; `orbitCodim H X x` |
| $c\_T(X)$; $c\_H(X)$ for a reductive group $H$ | `torusComplexity G X`; `complexity H X` |
| $X$ is normal; $X$ is toric | `X.IsNormal`; `IsToricVariety G X` |

The algebraic dimension is computed in real simple-root coordinates: the labels
of the Bruhat graph are the positive roots of the geometric realization of $W$
(`weylRealization`), which are positive multiples of the roots of $G$, so that
$\mathrm{AD}(u,v)$ and the spans of roots below have the dimensions of the
paper. The support `supportCard` counts the simple reflections below $w$ in the
Bruhat order, which are those that occur in a reduced word of $w$
(`supportCard_eq_card`). A variety is toric (`IsToricVariety`) if it is
irreducible, normal and of $T$-complexity $0$.

### Theorem 1.2: the torus complexity of Richardson varieties

For $u\le v\in W$, the $T$-complexity of the Richardson variety equals

$$
c\_T(\mathcal{R}\_{u,v})=\ell(v)-\ell(u)-\mathrm{ad}(u,v).
$$

Moreover, we have that

$$
\mathrm{ad}(u,v)=\max\_{u\le w\le v}\ell(v)-\ell(w)\quad\text{where }\mathcal{R}\_{w,v}\text{ is toric}.
$$

Here $\mathrm{AD}(u,v)$ is the real span of the labels $\mathrm{wt}(x,y)$ of the
edges of the Bruhat graph between $x$ and $y$ with $u\le x\lt y\le v$, the edge
between $w$ and $s\_\alpha w$, for $\alpha\in\Phi^+$, having label $\alpha$, and
$\mathrm{ad}(u,v)=\dim\mathrm{AD}(u,v)$ (Definition 3.2). The $T$-complexity is
the minimum codimension of a $T$-orbit (Definition 1.1).

The first formula is an identity of integers. The maximum is stated with
Mathlib's `IsGreatest`, so it is attained, and the toric varieties are those of
the Notation. Over $\mathbb{C}$ (`richardson_complexity_formula_complex`) the proof
follows the paper. The largest dimension of a $T$-orbit in $\mathcal{R}\_{u,v}$
is the dimension of the Bruhat interval polytope $Q\_{u,v}$, by the results of
Tsukerman and Williams that the paper cites, which are proved here
(*Bruhat interval polytopes*, Theorem 6.19 and Remark 7.11), and
$\dim Q\_{u,v}=\mathrm{ad}(u,v)$ (Proposition 3.3). The embedding of $G/B$
determined by $2\rho$ is realized in the projective space of
$\Lambda^d\mathfrak{g}$, with $d=\dim\mathfrak{b}$, by
$gB\mapsto g\cdot\Lambda^d\mathfrak{b}$. The orbit of largest dimension is the
orbit of a general point of $\mathcal{R}\_{u,v}$, at which the coordinates of
weight $z(2\rho)$ are nonzero for all $z\in\[u,v\]$, in place of the totally
positive point of the paper. The embedding is used for $G$ itself, without
passing to the simply connected cover of its derived subgroup.

Over every $K$, the largest orbit dimension is computed from the Deodhar
components instead, as in Theorem 1.4: every $T$-orbit of $\mathcal{R}\_{u,v}$
lies in an open Richardson variety $\mathcal{R}^\circ\_{x,y}$ with
$u\le x\le y\le v$, where Theorem 1.4 bounds its dimension by
$\mathrm{ad}(x,y)\le\mathrm{ad}(u,v)$, and a general point of the component of
the positive distinguished subword attains $\mathrm{ad}(u,v)$. In both cases
the second formula follows, as in the paper, from Proposition 3.12 and
Corollary 3.14, which uses the normality of Richardson varieties.

These declarations are in `SchubertOrbits`, `BruhatIntervals`, `GroupActions`
and `SchubertGeometry`
([StatementForms.lean](OrbitComplexity/Paper/StatementForms.lean),
[RichardsonComplexity.lean](OrbitComplexity/Paper/RichardsonComplexity.lean),
[ToricComplexity.lean](OrbitComplexity/Paper/ToricComplexity.lean),
[IntervalPolytopes.lean](OrbitComplexity/Paper/IntervalPolytopes.lean),
[Deodhar/RichardsonOrbits.lean](OrbitComplexity/Paper/Deodhar/RichardsonOrbits.lean),
[Graph/ToricMaxima.lean](OrbitComplexity/BruhatIntervals/Graph/ToricMaxima.lean),
[MomentMaps/OrbitFaces.lean](OrbitComplexity/GroupActions/MomentMaps/OrbitFaces.lean),
[Cells/RichardsonMoment.lean](OrbitComplexity/SchubertGeometry/Cells/RichardsonMoment.lean)).

| Declaration | Result |
| --- | --- |
| `richardson_complexity_formula` | All of Theorem 1.2 |
| `richardson_complexity_formula_complex` | Theorem 1.2 over $\mathbb{C}$, through the moment map |
| `richardson_orbit_maximum`, `richardson_orbit_maximum_complex` | Corollary 3.4: the largest dimension of a $T$-orbit in $\mathcal{R}\_{u,v}$ is $\mathrm{ad}(u,v)$ |
| `interval_polytope_span_dimension` | Proposition 3.3 |
| `projective_moment_faces` | Tsukerman–Williams, Theorem 6.19: the orbits in a torus orbit closure correspond to the faces of its moment polytope, with equal dimensions |
| `exists_richardson_moment_map` | Tsukerman–Williams, Remark 7.11: the moment image of $\mathcal{R}\_{u,v}$ is $Q\_{u,v}$, which is the moment image of the orbit closure of a general point |
| `toric_interval_maxima` | Proposition 3.12, with its dual and symmetric forms |
| `richardson_toric_criterion`, `richardson_toric_polytope` | Corollary 3.14: $\[u,v\]$ is toric iff $\mathcal{R}\_{u,v}$ is toric; Tsukerman–Williams, Proposition 7.12 |
| `schubert_richardson_normality` | Schubert varieties of $G/B$ and $G/P\_J$, and the $\mathcal{R}\_{u,v}$ with $u\le v$, are normal |

### Corollary 1.3: the torus complexity of Schubert varieties

For $w\in W$, the $T$-complexity of the Schubert variety $X\_w$ equals

$$
c\_T(X\_w)=\ell(w)-\mathrm{supp}(w).
$$

Here $\mathrm{supp}(w)$ is the number of simple reflections that appear in a
reduced word of $w$.

The corollary is an identity of integers, proved over every $K$ and over
$\mathbb{C}$ (`schubert_complexity_formula_complex`). As in the paper, it is the
case $u=\mathrm{id}$ of Theorem 1.2. The isomorphism
$\mathcal{R}\_{\mathrm{id},w}\cong X\_w$ is compatible with the inclusions in
$G/B$, hence with the torus actions, and
$\mathrm{ad}(\mathrm{id},w)=\mathrm{supp}(w)$, since
$\mathrm{AD}(\mathrm{id},w)$ is spanned by the simple roots of the support of
$w$.

These declarations are in `SchubertOrbits`, `BruhatIntervals` and
`SchubertGeometry`
([StatementForms.lean](OrbitComplexity/Paper/StatementForms.lean),
[Words/Support.lean](OrbitComplexity/BruhatIntervals/Words/Support.lean),
[Cells/RichardsonSchubert.lean](OrbitComplexity/SchubertGeometry/Cells/RichardsonSchubert.lean)).

| Declaration | Result |
| --- | --- |
| `schubert_complexity_formula` | All of Corollary 1.3 |
| `schubert_complexity_formula_complex` | Corollary 1.3 over $\mathbb{C}$ |
| `lower_support_span` | $\mathrm{AD}(\mathrm{id},w)$ is spanned by the simple roots of the support, and $\mathrm{ad}(\mathrm{id},w)=\mathrm{supp}(w)$ |
| `richardsonSchubertIso` | $\mathcal{R}\_{\mathrm{id},w}\cong X\_w$ |
| `supportCard_eq_card` | $\mathrm{supp}(w)$ is the number of distinct letters of any reduced word |

### Theorem 1.4: torus weights on Deodhar components

Fix $u\le v$ and fix a reduced word $\mathbf{v}$ of $v$. Let $\mathbf{u}$ be a
distinguished subword of $\mathbf{v}$ for $u$, and let $\mathbf{u}\_+$ be the
positive distinguished subword for $u$ in $\mathbf{v}$. For
$x\in D\_{\mathbf{u},\mathbf{v}}$, let $g$ be its standard form. Then

$$
\dim Tx=\dim\_{\mathbb{R}}\mathrm{span}\lbrace\beta\_k\mid k\in J\_{\mathbf{u}}^{\circ}\cup J\_{\mathbf{u}}^-,\ g^{(k)}\ne0\rbrace.
$$

In particular, $\dim Tx=\mathrm{td}(\mathbf{u},\mathbf{v})$ for a general point
$x$. Moreover, we have

$$
\mathrm{TD}(\mathbf{u},\mathbf{v})\subseteq\mathrm{TD}(\mathbf{u}\_+,\mathbf{v})=\mathrm{AD}(u,v).
$$

Here $D\_{\mathbf{u},\mathbf{v}}=G\_{\mathbf{u},\mathbf{v}}B/B$ is the Deodhar
component, where $G\_{\mathbf{u},\mathbf{v}}$ is the set of products
$g\_1\cdots g\_\ell$ of Definition 3.16, with parameters $p\_k\ne0$ for
$k\in J^\circ\_{\mathbf{u}}$ and $m\_k$ for $k\in J^-\_{\mathbf{u}}$; the
standard form of $x$ is the product $g$ with $x=gB$, and its coordinate
$g^{(k)}$ is $p\_k$ or $m\_k$; $\mathrm{TD}(\mathbf{u},\mathbf{v})$ is the real
span of the roots $\beta\_k$ for $k\in J^\circ\_{\mathbf{u}}\cup J^-\_{\mathbf{u}}$,
where $\beta\_k=u\_{(k-1)}(\alpha\_{i\_k})$ for $k\in J^\circ\_{\mathbf{u}}$ and
$\beta\_k=-u\_{(k-1)}(\alpha\_{i\_k})$ for $k\in J^-\_{\mathbf{u}}$, and
$\mathrm{td}(\mathbf{u},\mathbf{v})$ is its dimension (Definition 3.19); and $x$
is general if its parameters $m\_k$ are all nonzero.

A reduced word is a list of simple roots, a subword is a `Subexpression` of it,
and $u$ is its product. The theorem uses the parameter chart of
$D\_{\mathbf{u},\mathbf{v}}$: the open subvariety $\lbrace p\_k\ne0\rbrace$ of the
affine space with coordinates $p\_k$ and $m\_k$, on which $t\in T$ multiplies the
coordinate of index $k$ by the value at $t$ of the character $-\beta\_k$, with a
$T$-equivariant isomorphism onto $D\_{\mathbf{u},\mathbf{v}}$. Definition 3.16
(`deodharStandardForm_definition`) identifies $G\_{\mathbf{u},\mathbf{v}}$ with
the product of a split torus of rank $\lvert J^\circ\_{\mathbf{u}}\rvert$ and an
affine space of dimension $\lvert J^-\_{\mathbf{u}}\rvert$, and with
$D\_{\mathbf{u},\mathbf{v}}$. The weights of $T$ on
$Tx$ are the characters $-\beta\_k$ of the nonzero coordinates of $x$, as in the
proof of the paper. Their real span (`deodharComponentWeightSpan`) is the span
in the formula; it lies in $\mathrm{TD}(\mathbf{u},\mathbf{v})$ for every $x$ and
equals it for a general $x$. The general points form a nonempty dense open subset
(`deodharGeneralPoints`). The roots are taken in the real simple-root
coordinates of the Notation. In the last clause, $\mathbf{u}\_+$ is given as a
positive distinguished subword for $u$, which is unique by
`positive_subexpression_unique`. The theorem is proved over every $K$, and the
proof follows the paper, except that $\dim Tx$ is computed from the coordinate
algebra of the orbit instead of from its stabilizer.

These declarations are in `SchubertOrbits`, `BruhatIntervals` and
`SchubertGeometry`
([Deodhar/ComponentWeights.lean](OrbitComplexity/Paper/Deodhar/ComponentWeights.lean),
[Deodhar/Roots.lean](OrbitComplexity/Paper/Deodhar/Roots.lean),
[Deodhar/Spans.lean](OrbitComplexity/Paper/Deodhar/Spans.lean),
[StatementForms.lean](OrbitComplexity/Paper/StatementForms.lean),
[Words/Positive.lean](OrbitComplexity/BruhatIntervals/Words/Positive.lean),
[Deodhar/ComponentCover.lean](OrbitComplexity/SchubertGeometry/Deodhar/ComponentCover.lean)).

| Declaration | Result |
| --- | --- |
| `deodharComponent_weights` | All of Theorem 1.4 |
| `deodharComponentWeightSpan`, `deodharGeneralPoints` | The span of the weights on $Tx$; the general points |
| `subwordWeightSpan`, `subwordWeightSpan_interval` | $\mathrm{TD}(\mathbf{u},\mathbf{v})$, and $\mathrm{TD}(\mathbf{u},\mathbf{v})\subseteq\mathrm{AD}(u,v)$ with equality for positive subwords |
| `deodharComponent_orbit_le`, `deodharComponent_orbit_attains` | $\dim Tx\le\mathrm{td}(\mathbf{u},\mathbf{v})$, and the bound is attained |
| `positive_subexpression_unique` | The positive distinguished subword $\mathbf{u}\_+$ exists and is unique (Marsh–Rietsch, Lemma 3.5) |
| `deodharStandardForm_definition` | Definition 3.16: $G\_{\mathbf{u},\mathbf{v}}$, its parameters, and $G\_{\mathbf{u},\mathbf{v}}\cong D\_{\mathbf{u},\mathbf{v}}$ |
| `deodharStandard_partition`, `deodharRichardson_cover` | Theorem 3.17 (Deodhar): $\mathcal{R}^\circ\_{u,v}$ is the disjoint union of the $D\_{\mathbf{u},\mathbf{v}}$ |
| `deodharComponent_standardForm` | Lemma 3.20 |

### Theorem 1.5: Levi-Borel orbits and torus orbits

Let $w\in W$, $I\subseteq\Delta$, and let $w={}\_Iw\\,{}^Iw$ be the left parabolic
decomposition of $w$ with respect to $I$. The map
$\mathfrak{O}\colon\mathcal{O}\_T(X^\circ\_{{}^Iw})\to\mathcal{O}\_{B\_{L\_I}}(X^\circ\_w)$
given by $\Theta\mapsto B\_{L\_I}\\,{}\_Iw\\,x$, where $x$ is any point in $\Theta$,
is a surjection. If $L\_I$ acts on $X\_w$, then $\mathfrak{O}$ is a codimension
preserving bijection. That is,

$$
\dim(X^\circ\_w)-\dim(\mathfrak{O}(\Theta))=\dim(X^\circ\_{{}^Iw})-\dim(\Theta),
$$

for every $\Theta\in\mathcal{O}\_T(X^\circ\_{{}^Iw})$.

Here ${}\_Iw\in W\_I$, ${}^Iw$ is the minimal representative of the coset
$W\_Iw$, $L\_I$ is the Levi subgroup of the standard parabolic subgroup $P\_I$,
$B\_{L\_I}=L\_I\cap B$, and $\mathcal{O}\_H(X)$ is the set of $H$-orbits in $X$.

The sets of orbits are quotients of the sets of $K$-points by the orbit
relations. The map is given on representatives: for each point $x$ of
$X^\circ\_{{}^Iw}$ the theorem provides a point of $X^\circ\_w$ whose image in
$G/B$ is ${}\_Iw\cdot x$, for the fixed representative of ${}\_Iw$, and the map
sends the orbit of $x$ to the $B\_{L\_I}$-orbit of that point. That $L\_I$ acts on
$X\_w$ means that there is an action of $L\_I$ on the scheme $X\_w$ for which the
closed immersion $X\_w\to G/B$ is equivariant; by Theorem 1.6 this holds exactly
when $I\subseteq\mathcal{D}\_L(w)$. The codimensions are the integers
`orbitCodim`.

As in the paper, the proof goes through the $I$-heart
$\mathrm{Heart}\_I(X\_w)=V\_dwB\subseteq X^\circ\_w$ (Definition 4.1), which is
$T$-equivariantly isomorphic to $X^\circ\_{{}^Iw}$ with the twisted action
$\cdot\_{a^{-1}}$ (Proposition 4.2) and meets every $B\_{L\_I}$-orbit of
$X^\circ\_w$ (Lemma 4.6); its $T$-orbits correspond to the $B\_{L\_I}$-orbits of
$X^\circ\_w$ (Theorem 4.7).

These declarations are in `SchubertOrbits`
([Heart/LeviOrbitStatements.lean](OrbitComplexity/Paper/Heart/LeviOrbitStatements.lean),
[Heart/Definition.lean](OrbitComplexity/Paper/Heart/Definition.lean),
[Heart/Isomorphism.lean](OrbitComplexity/Paper/Heart/Isomorphism.lean),
[Heart/Meeting.lean](OrbitComplexity/Paper/Heart/Meeting.lean),
[Heart/ComplementEquivalences.lean](OrbitComplexity/Paper/Heart/ComplementEquivalences.lean),
[Complex/TwistedCells.lean](OrbitComplexity/Paper/Complex/TwistedCells.lean)).

| Declaration | Result |
| --- | --- |
| `torus_levi_orbits` | All of Theorem 1.5 |
| `torus_levi_orbits_complex` | Theorem 1.5 over $\mathbb{C}$ |
| `heart_levi_orbits` | Theorem 4.7: the same correspondence from the $T$-orbits of $\mathrm{Heart}\_I(X\_w)$ |
| `heart`, `heart_equivariant_iso` | Definition 4.1 and Proposition 4.2 |
| `leviBorel_orbit_meets_heart` | Lemma 4.6 |
| `complement_equivalences` | Lemma 4.3: $L\_I$ acts on $X\_w$ iff $I\subseteq\mathcal{D}\_L(w)$ iff ${}\_Iw=w\_0(I)$, and the other equivalent conditions |
| `twistedActions_schubert` | The twisted actions $\cdot\_u$ (Gao–Hodges–Yong, Lemmas 3.1 and 3.2) |

### Theorem 1.6: the Levi complexity of Schubert varieties

Let $w\in W$ and suppose $L\_I$ acts on the Schubert variety $X\_w$, or
equivalently $I\subseteq\mathcal{D}\_L(w)$. If $w={}\_Iw\\,{}^Iw$ is the left
parabolic decomposition of $w$ with respect to $I$, then

$$
c\_{L\_I}(X\_w)=\ell({}^Iw)-\mathrm{supp}({}^Iw).
$$

Here $\mathcal{D}\_L(w)$ is the left descent set of $w$, and $c\_{L\_I}(X\_w)$ is
the minimum codimension of a $B\_{L\_I}$-orbit in $X\_w$.

The theorem has two parts: an action of $L\_I$ on $X\_w$, in the sense of
Theorem 1.5, exists if and only if $I\subseteq\mathcal{D}\_L(w)$, and the formula
holds for every such action. The group $L\_I$ is a connected reductive group
with Borel subgroup $B\_{L\_I}$, and $c\_{L\_I}$ is its complexity. The equivalence
comes from the stabilizer of $X\_w$, which is $P\_{\mathcal{D}\_L(w)}$
(Billey–Lakshmibai, Lemma 8.2.3, proved here). The formula is proved as in the
paper: by Theorem 1.5 the minimal codimension of a $B\_{L\_I}$-orbit in
$X^\circ\_w$ is $c\_T(X^\circ\_{{}^Iw})$ (Corollary 4.8), which equals
$c\_T(X\_{{}^Iw})$; Proposition 4.9 bounds the codimensions of the orbits in the
smaller cells $X^\circ\_u$, $u\le w$; and Corollary 1.3 evaluates
$c\_T(X\_{{}^Iw})$.

These declarations are in `SchubertOrbits` and `SchubertGeometry`
([Heart/LeviComplexityFormula.lean](OrbitComplexity/Paper/Heart/LeviComplexityFormula.lean),
[Heart/LeviMinimum.lean](OrbitComplexity/Paper/Heart/LeviMinimum.lean),
[Heart/CodimensionBounds.lean](OrbitComplexity/Paper/Heart/CodimensionBounds.lean),
[Heart/LeviClosureComplexity.lean](OrbitComplexity/Paper/Heart/LeviClosureComplexity.lean),
[Parabolics/LeviStability.lean](OrbitComplexity/SchubertGeometry/Parabolics/LeviStability.lean),
[Parabolics/Stabilizer.lean](OrbitComplexity/SchubertGeometry/Parabolics/Stabilizer.lean)).

| Declaration | Result |
| --- | --- |
| `levi_complexity_properties` | All of Theorem 1.6 |
| `levi_complexity_properties_complex` | Theorem 1.6 over $\mathbb{C}$ |
| `levi_schubert_action_iff`, `schubert_stabilizer_levi` | $L\_I$ acts on $X\_w$ iff $I\subseteq\mathcal{D}\_L(w)$; the stabilizer of $X\_w$ is $P\_{\mathcal{D}\_L(w)}$ |
| `levi_cell_minOrbitCodim` | Corollary 4.8 |
| `levi_orbit_codimension_bounds` | Proposition 4.9 |
| `levi_complexity_eq_minimal` | $c\_{L\_I}(X\_w)=c\_T(X\_{{}^Iw})$ |

### Theorem 4.11 and Corollary 4.12: partial flag varieties

Let $w\in W^J$ and $I\subseteq\mathcal{D}\_L(ww\_0(J))$. Then $L\_I$ acts on
$X^{P\_J}\_w$. If $L\_I$ also acts on $X\_w$, or equivalently if
$I\subseteq\mathcal{D}\_L(w)$, then $c\_{L\_I}(X^{P\_J}\_w)=c\_{L\_I}(X\_w)$
(Theorem 4.11).

Let $w\in W^J$. Then $c\_T(X^{P\_J}\_w)=c\_T(X\_w)$. In particular, $X^{P\_J}\_w$ is a
toric variety if and only if each $s\_j\in S$ appears at most once in any
reduced expression of $w$, or equivalently, $\ell(w)=\mathrm{supp}(w)$
(Corollary 4.12).

Here $W^J$ is the set of minimal representatives of the cosets $wW\_J$,
$w\_0(J)$ is the longest element of $W\_J$, and $X^{P\_J}\_w$ is the closure of
$BwP\_J/P\_J$ in the partial flag variety $G/P\_J$.

The partial flag variety (`partialFlagVariety`) is the orbit of a point of a
projective space under $G$; it is projective, its $K$-points are the cosets
$gP\_J$, and the projection $G/B\to G/P\_J$ is proper and equivariant. As in the
paper, $L\_I$ acts on $X^{P\_J}\_w$ because its stabilizer is
$P\_{\mathcal{D}\_L(ww\_0(J))}$ (Lemma 4.10), and the complexities agree because
the projection restricts to an $L\_I$-equivariant birational morphism
$X\_w\to X^{P\_J}\_w$, and complexity is invariant under equivariant birational
maps (Pezzini, §2). This invariance is proved here from Rosenlicht's theorem.
Theorem 4.11 also records the case of the empty set $I$, where
$L\_I=B\_{L\_I}=T$. In Corollary 4.12 the
toric varieties include normality, which is proved for the Schubert varieties of
every partial flag variety, and the condition on reduced expressions is stated
for every reduced word of $w$.

These declarations are in `SchubertOrbits`, `GroupActions`, `BruhatIntervals`
and `SchubertGeometry`
([Complex/PartialSchubert.lean](OrbitComplexity/Paper/Complex/PartialSchubert.lean),
[ToricComplexity.lean](OrbitComplexity/Paper/ToricComplexity.lean),
[Rosenlicht/ReductiveComplexity.lean](OrbitComplexity/GroupActions/Rosenlicht/ReductiveComplexity.lean),
[Words/Distinct.lean](OrbitComplexity/BruhatIntervals/Words/Distinct.lean),
[Parabolics/Stability.lean](OrbitComplexity/SchubertGeometry/Parabolics/Stability.lean),
[Parabolics/Geometry.lean](OrbitComplexity/SchubertGeometry/Parabolics/Geometry.lean),
[Normality/PartialNormalDescent.lean](OrbitComplexity/SchubertGeometry/Normality/PartialNormalDescent.lean)).

| Declaration | Result |
| --- | --- |
| `partial_schubert_levi` | All of Theorem 4.11, with the case of the empty set $I$ |
| `partial_schubert_toric` | All of Corollary 4.12 |
| `partial_schubert_levi_complex`, `partial_schubert_toric_complex` | Theorem 4.11 and Corollary 4.12 over $\mathbb{C}$ |
| `partialSchubertStabilizer_eq` | Lemma 4.10: the stabilizer of $X^{P\_J}\_w$ is $P\_{\mathcal{D}\_L(ww\_0(J))}$ |
| `partialFlag_properties` | $G/P\_J$ is projective, and the projection $G/B\to G/P\_J$ restricts to birational morphisms $X\_w\to X^{P\_J}\_w$ |
| `complexity_eq_of_birational` | Complexity is invariant under equivariant birational maps |
| `distinct_reduced_words` | $\ell(w)=\mathrm{supp}(w)$ iff every reduced word of $w$ has distinct letters |
| `partialSchubert_normal_stalks` | Schubert varieties in $G/P\_J$ are normal |

### Every other statement

Every other statement of the paper is formalized: the definitions of
Sections 1 to 4, the lemmas and propositions behind the main theorems,
Examples 3.9 and 3.18 and the remarks of Section 3.1, the displayed equations
its proofs use, the claims made in its prose, and the results it cites, among
them the normality of Schubert varieties in every partial flag variety and of
Richardson varieties, Deodhar's decomposition, the moment-map results of
Tsukerman and Williams, Dyer's results on the Bruhat graph, the stabilizers of
Schubert varieties, Brion's formula for the dimension of an orbit, and the
invariance of complexity under equivariant birational maps.
[docs/STATEMENTS.md](docs/STATEMENTS.md) lists each of them, in the order of
the paper, with its Lean declarations. Two results that the paper quotes and no
proof uses are not formalized: the theorem of Can and Saha in the remark after
Definition 3.11, and the Cohen–Macaulay property and rational singularities of
Schubert and Richardson varieties.

## Libraries

The Lean library `OrbitComplexity` is divided into seven parts. The first six
are general and do not import the seventh, which contains the paper.
`ReductiveGroups` builds on `FlagVarieties`, `GroupActions` on
`ReductiveGroups`, and `SchubertGeometry` on the other five. The results of
other papers that the paper cites are proved in these libraries, in general
form, so a project can use them by importing the library, without the paper:
the normality of Schubert and Richardson varieties (`SchubertGeometry`, through
`FrobeniusSplitting`), Deodhar's decomposition (`SchubertGeometry`), Brion's
orbit dimension formula and Rosenlicht's theorem (`GroupActions`), and the
moment-map results of Tsukerman and Williams (`GroupActions` and
`SchubertGeometry`).

### The FlagVarieties library

[OrbitComplexity/FlagVarieties/](OrbitComplexity/FlagVarieties) (namespace
`FlagVarieties`, 15 files) proves the Bruhat decomposition of invertible
matrices over a field: every invertible $n\times n$ matrix is the product of an
invertible upper triangular matrix, a permutation matrix and an invertible upper
triangular matrix. The proof isolates a nonzero pivot in the bottom row,
factors the complementary minor by induction and reinserts the pivot.

| Declaration | Result |
| --- | --- |
| `FlagVarieties.Foundations.TypeA.exists_upper_perm_upper_of_isUnit` | The Bruhat decomposition of an invertible matrix |
| `FlagVarieties.Foundations.pivotMatrix` | Partial permutation matrices |

### The ReductiveGroups library

[OrbitComplexity/ReductiveGroups/](OrbitComplexity/ReductiveGroups) (namespace
`ReductiveGroups`, 557 files) develops connected reductive groups over a field,
given by their coordinate Hopf algebras with a Borel subgroup and a split
maximal torus: tori and their characters, Borel and unipotent subgroups,
centralizers and normalizers, root subgroups and their additive parameters,
coroots and the homomorphisms from $\mathrm{SL}\_2$ attached to simple roots,
representations and the adjoint action; the Lie algebra, its Cartan subalgebra
and the root system of $G$ relative to $T$, with the base determined by $B$ and
Chevalley systems; the Weyl group as a Coxeter group on the simple reflections,
with its longest element, inversion sets, supports and parabolic decompositions;
standard parabolic and Levi subgroups; and the general linear group.

| Declaration | Result |
| --- | --- |
| `ReductiveGroups.ReductiveGroupData` | A connected reductive group with a Borel subgroup and a split maximal torus |
| `ReductiveGroups.ReductiveGroupData.rootSystem`, `ReductiveGroups.ReductiveGroupData.rootBase` | The root system of $(G,T)$ and the base determined by $B$ |
| `ReductiveGroups.weylCoxeterSystem`, `ReductiveGroups.weylCoxeterPresentationEquiv` | The Weyl group has the Coxeter presentation on its simple reflections |
| `ReductiveGroups.ReductiveGroupData.existsUnique_rootParameter` | Each vector of a root space is the differential of a unique homomorphism $\mathbb{G}\_a\to G$ |
| `ReductiveGroups.ReductiveGroupData.exists_simpleSl2Map` | For each simple root, a homomorphism $\mathrm{SL}\_2\to G$ through the root subgroups of $\alpha\_i$ and $-\alpha\_i$ |
| `ReductiveGroups.ReductiveGroupData.exists_chevalleySystem` | Chevalley systems |
| `ReductiveGroups.RootInversionCount.leftParabolic_decomposition` | $\ell(w)=\ell({}\_Iw)+\ell({}^Iw)$ |
| `ReductiveGroups.bruhat_longest_mul_iff` | $w\_0u\le w\_0v$ iff $v\le u$ |
| `ReductiveGroups.GLn.groupData` | $\mathrm{GL}\_n$ with its diagonal torus and upper triangular Borel subgroup |

### The BruhatIntervals library

[OrbitComplexity/BruhatIntervals/](OrbitComplexity/BruhatIntervals) (namespace
`BruhatIntervals`, 91 files) develops Coxeter systems, in the sense of Mathlib,
with a geometric realization by reflections on a real vector space: roots,
reflections, inversion sets and their behaviour under length-additive
products; reduced words, subexpressions and their distinguished and positive
forms, the subword and lifting properties, supports, descents and parabolic
decompositions; Bruhat intervals, their chains and covers, and the intervals of
rank two; the Bruhat graph with its root labels, the real span of the labels of
an interval and its algebraic dimension, their recursions, and toric
subintervals; reflection subgroups and the equality of root planes of equal
reflection products; interval polytopes; and the symmetric group as a Coxeter
group.

| Declaration | Result |
| --- | --- |
| `BruhatIntervals.Realization` | Geometric realizations of a Coxeter system |
| `BruhatIntervals.subexpression_subword_property`, `BruhatIntervals.lifting_property` | The subword and lifting properties |
| `BruhatIntervals.bruhatGraph`, `BruhatIntervals.edgeLabel` | The Bruhat graph and its root labels |
| `BruhatIntervals.labelSpan`, `BruhatIntervals.algebraicDim`, `BruhatIntervals.algebraicDim_le_length` | $\mathrm{AD}(u,v)$, $\mathrm{ad}(u,v)$, and $\mathrm{ad}(u,v)\le\ell(v)-\ell(u)$ |
| `BruhatIntervals.labelSpan_eq_covers`, `BruhatIntervals.labelSpan_recursion` | $\mathrm{AD}(u,v)$ is spanned by the labels of covers, and its recursion at a right descent of $v$ |
| `BruhatIntervals.toric_interval_maxima` | $\mathrm{ad}(u,v)$ is the largest length of a toric lower, upper or arbitrary subinterval |
| `BruhatIntervals.Realization.rootProduct_span` | Equal products of two reflections have equal two-dimensional root planes (Dyer) |
| `BruhatIntervals.positive_subexpression_unique` | Unique positive distinguished subexpressions (Marsh–Rietsch) |
| `BruhatIntervals.distinct_reduced_words` | $\ell(w)=\mathrm{supp}(w)$ iff every reduced word of $w$ has distinct letters |
| `BruhatIntervals.intervalPolytope_finDim` | A regular interval polytope has dimension $\mathrm{ad}(u,v)$ |

### The GroupActions library

[OrbitComplexity/GroupActions/](OrbitComplexity/GroupActions) (namespace
`GroupActions`, 364 files) develops varieties over a field, as reduced
separated schemes of finite type, with their rational points, dimensions and
normality, and actions of algebraic groups on them: orbits, their closures and
stabilizers, and the dimension formula for orbits; the complexity of an action
of a reductive group, and spherical and toric varieties; Rosenlicht's theorem on
invariant rational functions, and the invariance of complexity under
equivariant birational maps; torus orbits and the ranks of their weights; and
projective representations and the moment map of a complex torus
representation, with the correspondence between the orbits in a torus orbit
closure and the faces of its moment polytope.

| Declaration | Result |
| --- | --- |
| `GroupActions.Variety` | Varieties over a field |
| `GroupActions.orbit_dimension_formula` | Orbits are locally closed, and $\dim Hx=\dim H-\dim H\_x$ |
| `GroupActions.complexity`, `GroupActions.complexity_definition` | The complexity: the minimum codimension of an orbit of a Borel subgroup |
| `GroupActions.IsSpherical`, `GroupActions.IsToricVariety`, `GroupActions.spherical_toric_definition` | Spherical and toric varieties |
| `GroupActions.Variety.minOrbitCodim_eq_trdeg` | Rosenlicht's theorem: the minimum codimension of an orbit is the transcendence degree of the invariant rational functions |
| `GroupActions.complexity_eq_of_birational` | Complexity is invariant under equivariant birational maps |
| `GroupActions.torus_orbit_dim` | The orbit of a point under a diagonal torus action has the dimension of the span of the weights of its nonzero coordinates |
| `GroupActions.momentMap`, `GroupActions.projective_moment_faces` | The moment map, and the orbits in a torus orbit closure correspond to the faces of its moment polytope |

### The FrobeniusSplitting library

[OrbitComplexity/FrobeniusSplitting/](OrbitComplexity/FrobeniusSplitting)
(namespace `FrobeniusSplitting`, 431 files) develops Frobenius splittings:
Frobenius-linear retractions of the Frobenius map of a commutative semiring,
and their sheaf versions on schemes, with localization, gluing, restriction,
stalks and pushforward; the splittings of polynomial, Laurent and group
algebras and of tensor products, and the Cartier trace; compatibly split ideals
and closed subschemes, which are radical and whose minimal primes are again
compatible; and normality: a split domain of finite type that is properly
dominated, with geometrically connected fibres, by a normal integral scheme is
normal, and an integral scheme over a field is normal when it has a model over
a finitely generated subring whose fibres of positive characteristic are
irreducible and normal.

| Declaration | Result |
| --- | --- |
| `FrobeniusSplitting.RingSplitting`, `FrobeniusSplitting.SchemeSplitting` | Frobenius splittings of commutative semirings and of schemes |
| `FrobeniusSplitting.RingSplitting.isReduced` | A split ring is reduced |
| `FrobeniusSplitting.RingSplitting.IsCompatible.isRadical`, `FrobeniusSplitting.RingSplitting.compatible_minimalPrime` | Compatible ideals are radical, and minimal primes are compatible |
| `FrobeniusSplitting.SchemeSplitting.pushforward` | Splittings descend along morphisms $f\colon X\to Y$ with $\mathcal{O}\_Y\cong f\_\*\mathcal{O}\_X$ |
| `FrobeniusSplitting.isIntegrallyClosed_of_proper` | Normality of split domains dominated by normal schemes |
| `FrobeniusSplitting.normal_stalks_of_positive_fibres` | Normality from the fibres of positive characteristic of a model |

### The SchubertGeometry library

[OrbitComplexity/SchubertGeometry/](OrbitComplexity/SchubertGeometry)
(namespace `SchubertGeometry`, 892 files) develops the geometry of a connected
reductive group over an algebraically closed field of characteristic zero and
its flag variety: $G/B$ as a scheme glued from translates of the big cell,
smooth and proper of dimension $\ell(w\_0)$; the Bruhat decomposition and
$W\cong N\_G(T)/T$; Schubert cells and varieties, opposite Schubert varieties,
Richardson varieties and their open cells, with the closure order, dimensions
and irreducibility; the affine structure of Schubert cells; Deodhar components
and Deodhar's decomposition of open Richardson varieties; standard parabolic and
Levi subgroups, the stabilizers of Schubert varieties, and partial flag
varieties with their Schubert varieties; Bott–Samelson–Demazure–Hansen
resolutions; line bundles and Frobenius splittings, in positive characteristic,
of models of the flag variety and of these resolutions, compatible with all
Schubert and opposite Schubert varieties; from them, the normality of Schubert
varieties in $G/B$ and in $G/P\_J$ and of Richardson varieties; and the moment
map of the complex flag variety.

| Declaration | Result |
| --- | --- |
| `SchubertGeometry.flagVariety`, `SchubertGeometry.flagVariety_isProper`, `SchubertGeometry.flagVariety_smooth`, `SchubertGeometry.flagVariety_dim` | The flag variety: proper and smooth, of dimension $\ell(w\_0)$ |
| `SchubertGeometry.bruhatDecomposition`, `SchubertGeometry.bruhatDecomposition_unique`, `SchubertGeometry.weylQuotientEquiv` | Each point of $G$ lies in exactly one double coset $BwB$; $W\cong N\_G(T)/T$ |
| `SchubertGeometry.richardson_structure` | Closure order, nonemptiness, irreducibility, dimension and strata of Richardson varieties |
| `SchubertGeometry.deodharRichardson_cover` | The Deodhar components cover the open Richardson variety |
| `SchubertGeometry.schubert_stabilizer_levi` | The stabilizer of $X\_w$ is $P\_{\mathcal{D}\_L(w)}$ |
| `SchubertGeometry.partialFlagVariety`, `SchubertGeometry.partialFlag_properties` | Partial flag varieties, projective, with the projection from $G/B$ |
| `SchubertGeometry.bsdhScheme`, `SchubertGeometry.bsdh_longest_birational` | Bott–Samelson–Demazure–Hansen schemes, birational onto $G/B$ for a reduced word of $w\_0$ |
| `SchubertGeometry.normal_stalks_of_split_resolutions` | Normality from a resolution and split fibres of positive characteristic |
| `SchubertGeometry.schubert_normal_stalks`, `SchubertGeometry.partialSchubert_normal_stalks`, `SchubertGeometry.richardson_normal_stalks` | Schubert varieties in $G/B$ and $G/P\_J$, and Richardson varieties, are normal |
| `SchubertGeometry.exists_richardson_moment_map` | The moment image of a complex Richardson variety is its Bruhat interval polytope |

Each of the six general libraries is at version 0.1.0 and imports only Mathlib,
Tau Ceti and the libraries it builds on.
[LIBRARY_MANIFEST.json](LIBRARY_MANIFEST.json) records their folders and the
SHA-256 hash of every file.

### The paper

[OrbitComplexity/Paper/](OrbitComplexity/Paper) (namespace `SchubertOrbits`,
112 files) contains every result of the paper, as described above: the root
subgroups of Section 2.2, the interval polytopes and Richardson complexities of
Section 3, the Deodhar components of Section 3.2, the hearts and Levi-Borel
orbits of Sections 4.1 and 4.2, and the partial flag varieties of Section 4.3,
with the statements over $\mathbb{C}$.

## Build and verify

Install [Lean and Lake through elan](https://lean-lang.org/install/) and
[Python 3](https://www.python.org/downloads/). Git must also be available.
The `lean-toolchain` file selects Lean 4.35.0-rc3 automatically, and
`lake-manifest.json` pins Mathlib, Tau Ceti and their public dependencies.

From the repository directory, run:

```text
lake exe cache get
python build.py --jobs 3
lake env lean OrbitComplexity/Paper/Audit.lean
```

On Windows, `py -3` can replace `python`; a short project path is recommended.
The first setup requires internet access and space for Lean and Mathlib.
The first command downloads public dependency caches. The Python helper first
has Lake build the Tau Ceti modules used here, then recompiles all
**2463 local Lean modules** in dependency order, and exits with a
nonzero status if a module fails. With three jobs the full build takes about
6 hours on a laptop.

To resume an interrupted build, or to check that every module was compiled
from the current sources:

```text
python build.py --jobs 3 --resume
python build.py --check
```

A standard `lake build` target is also configured.

The audit prints the transitive axiom dependencies of every declaration listed
in [docs/STATEMENTS.md](docs/STATEMENTS.md). The expected axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

Recorded checks:

- [provenance/BUILD_CHECK.json](provenance/BUILD_CHECK.json)
- [provenance/ENDPOINT_AUDIT.txt](provenance/ENDPOINT_AUDIT.txt)

To check the distributed snapshot's hashes and the local import completeness:

```text
python verify_bundle.py
```

`SHA256SUMS.json` describes this release snapshot. Intentional edits require
updating the hash inventory before that integrity check can pass again.

## Source layout

- `OrbitComplexity/FlagVarieties/`: the Bruhat decomposition of invertible
  matrices.
- `OrbitComplexity/ReductiveGroups/`: reductive groups. `Groups` covers tori,
  Borel, unipotent and root subgroups, $\mathrm{SL}\_2$ homomorphisms,
  representations and the reductive groups themselves; `Lie` covers Cartan
  subalgebras, root spaces and exponentials; `Roots` covers root data, Weyl
  groups as Coxeter groups, inversions, supports and parabolic decompositions;
  `GLn` covers the general linear group.
- `OrbitComplexity/BruhatIntervals/`: Coxeter combinatorics. `Order` and
  `Intervals` cover the Bruhat order and its intervals; `Words` covers reduced
  words and subexpressions; `Realizations` and `ReflectionSubgroups` cover
  roots and reflection subgroups; `Graph` covers the Bruhat graph, label spans,
  toric intervals and interval polytopes; `Permutations` covers the symmetric
  group.
- `OrbitComplexity/GroupActions/`: varieties and group actions. `Varieties`,
  `Actions` and `Complexity` cover varieties, orbits and complexity;
  `Rosenlicht` covers invariant rational functions; `Tori` covers torus orbits;
  `Representations` and `MomentMaps` cover projective representations and moment
  maps.
- `OrbitComplexity/FrobeniusSplitting/`: Frobenius splittings. `Splittings`,
  `Compatible`, `Cartier` and `Modules` cover splittings, compatible ideals, the
  Cartier trace and sheaves of Frobenius-linear operators; `Normality` covers
  the normality criteria and arithmetic models.
- `OrbitComplexity/SchubertGeometry/`: flag geometry. `FlagVariety` and `Cells`
  cover the flag variety and its Schubert and Richardson strata; `Groups` and
  `Roots` cover $W\cong N\_G(T)/T$ and root subgroups; `Deodhar` covers Deodhar
  components; `Parabolics` and `Levi` cover parabolic and Levi subgroups and
  partial flag varieties; `ProjectiveLine`, `IntegralProjectiveLine`,
  `FlagBundle` and `BSDH` cover the Schubert curves, the bundles over the flag
  variety and the Bott–Samelson–Demazure–Hansen resolutions; `LineBundles`,
  `Frobenius`, `Connectedness` and `Normality` cover the proof of normality.
- `OrbitComplexity/Paper/`: the paper. `Roots` covers the root subgroups of
  Section 2.2; `IntervalPolytopes.lean`, `RichardsonComplexity.lean` and
  `ToricComplexity.lean` prove Proposition 3.3, Corollary 3.4 over
  $\mathbb{C}$, Corollary 3.14, the complexity formulas of Theorem 1.2 and
  Corollary 1.3, and Corollary 4.12; `BruhatExamples` works Example 3.9 and the
  remark after Definition 3.11; `Deodhar` covers Section 3.2, with Theorem 1.4,
  Lemma 3.20, Example 3.18 and Corollary 3.4 over every $K$; `Heart` proves
  Theorems 1.5, 1.6 and 4.7 and the other results of Sections 4.1 and 4.2;
  `Complex` states the results over $\mathbb{C}$ and proves Theorem 4.11
  (Section 4.3); `StatementForms.lean` states the entries that combine several
  clauses.
- `OrbitComplexity/Paper/Main.lean`: imports every result of the paper; the
  root module `OrbitComplexity.lean` imports every library.
- `OrbitComplexity/Paper/Audit.lean`: the audit described above, with its two
  modules `CombinatoricsAudit.lean` and `GeometryAudit.lean`.
- `LIBRARY_MANIFEST.json`: the version, folders and file hashes of the general
  libraries.
- `docs/STATEMENTS.md`: the statements of the paper and their Lean
  counterparts.
- `docs/NORMALITY_DECLARATIONS.md`: the declarations of the proof that
  Schubert and Richardson varieties are normal.
- `provenance/`: source inventory and verification records.

## Attribution and licensing

This repository is licensed under the [Apache License 2.0](LICENSE).
Redistributions must retain the [NOTICE](NOTICE) file. If you use or adapt
this code, please cite this repository; citation metadata is in
[CITATION.cff](CITATION.cff).

Three files of the reductive-group library are adapted from sources under the
**Apache License 2.0**:
[Groups/Diagonal/DiagonalMatrixTorus.lean](OrbitComplexity/ReductiveGroups/Groups/Diagonal/DiagonalMatrixTorus.lean)
and
[Groups/Representations/GeneralLinearAdjointMatrix.lean](OrbitComplexity/ReductiveGroups/Groups/Representations/GeneralLinearAdjointMatrix.lean)
from Tau Ceti (the Tau Ceti contributors), and
[Lie/Basis/Equivalence.lean](OrbitComplexity/ReductiveGroups/Lie/Basis/Equivalence.lean)
from Mathlib's `Mathlib/Algebra/Lie/Basis/Prod.lean` (Oliver Nash). Their
headers keep the original copyright notices, and each file names its source.

Mathlib, Tau Ceti and their dependencies are downloaded by Lake at pinned
revisions and keep their own licenses; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
