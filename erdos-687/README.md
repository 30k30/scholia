# Erdős #687 from the quadratic Jacobsthal bound

HJ van Veen ([@30k30](https://github.com/30k30)), October 2026. The Lean bridge was written with Claude (Anthropic).

## Statement

Let $Y(x)$ be the largest $y$ such that one residue class $a_p \bmod p$ for each prime
$p \le x$ can cover every integer in $[1, y]$. Erdős (1980) asked for good estimates of $Y(x)$;
[Erdős #687](https://www.erdosproblems.com/687) asks in particular whether $Y(x) = o(x^2)$.
The same question is [Ben Green's Open Problem 46](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.46).
The best upper bound had been Iwaniec's $Y(x) \ll x^2$ (1978).

**Answer.** $Y(x) \ll x^2 / \big((\log x)^2 (\log\log x)^2\big)$; in particular $Y(x) = o(x^2)$.

## Proof

OpenAI's manuscript *A quadratic bound for Jacobsthal's function*
([paper](https://github.com/openai/math/blob/main/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf),
release item 021, a solution to [Erdős #970](https://www.erdosproblems.com/970)) proves

$$h(k) \le C\,\frac{k^2}{(\log\log 3k)^2},$$

where $h(k)$ is the least $m$ such that every $m$ consecutive integers contain one coprime to any
given integer with at most $k$ distinct prime factors.

Let $P(x) = \prod_{p \le x} p$. Given a covering of $[1, y]$, the Chinese remainder theorem gives
an integer $A$ with $A \equiv a_p \pmod p$ for every $p \le x$. Then each of the $y$ consecutive
integers $n - A$, $1 \le n \le y$, shares a prime factor with $P(x)$. So $y < j(P(x)) \le h(\pi(x))$,
which is the identity $Y(x) = j(P(x)) - 1$ of Ford–Green–Konyagin–Maynard–Tao
(*Long gaps between primes*, 2018, eq. (1.3)). With $\pi(x) \le x + 1$ the bound follows.

In the inverse form of Erdős's 1980 survey, where $f(x)$ is the least bound such that the primes
below $f(x)$ can cover every $n < x$, this reads $f(x) \gg x^{1/2} \log x \log\log x$.

The reduction for Green 46 was noted independently in
[formal-conjectures issue #6908](https://github.com/google-deepmind/formal-conjectures/issues/6908)
(7 Oct 2026), which also flags that the step is not part of OpenAI's Lean proof. This folder supplies it.

## What is checked in Lean

`bridge/Erdos687/Bridge.lean` uses only Mathlib. It takes the Jacobsthal bound as a hypothesis,
stated literally as `JacobsthalIteratedLogStatement` (the release's comparator statement with its
definitions written out), and proves:

- `Erdos687.little_o`: for every $\varepsilon > 0$ and all large $x$, any covering of $[1, y]$ by one
  class per prime $p \le x$ has $y \le \varepsilon x^2$;
- `Green46.improve_upper`: formal-conjectures' `green_46.improve_upper`, against their definitions
  copied verbatim, with answer $(x+1)^2/(\log\log 3(x+1))^2$;
- `FC970.erdos_970_rhs`: the right-hand side of formal-conjectures' `erdos_970`, from the quadratic bound.

`bridge/Erdos687/FormalConjectures.lean` restates these in exactly the form used in
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures), with the same
definitions and declaration names:

- `green_46.improve_upper` from `GreensOpenProblems/46.lean`, in the repository's
  `<theorem>.answer` convention (PR [#7183](https://github.com/google-deepmind/formal-conjectures/pull/7183));
- `erdos_687.parts.ii` from `ErdosProblems/687.lean` by Daniel Veljjanoski
  (PR [#6864](https://github.com/google-deepmind/formal-conjectures/pull/6864)).

Compiled inside a copy of formal-conjectures at `main` (with its own attributes and linters), each
repository statement was checked to be the same term (`rfl`) as the statement proved here.
An earlier version, matching the `687.lean` first proposed in #7183, is at commit
[`af06f47`](https://github.com/30k30/scholia/tree/af06f47d8ccf2247a3d1ebbb97fa261d103e7f83/erdos-687).

`glue/JacobsthalTo687.lean` plugs in the release's theorems
`OAI.Erdos970.Erdos970Final.erdos_970_iterated_log` and `erdos_970_quadratic`, and proves all of
the above unconditionally. Result (`logs/bridge.log`):

    'erdos_970_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
    'erdos_687_little_o' depends on axioms: [propext, Classical.choice, Quot.sound]
    'green_46_improve_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Green46.green_46.improve_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Erdos687.erdos_687.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]

The release's own comparator challenges for item 021 also pass (`logs/comparator_*.log`):
"Lean default kernel accepts the solution".

The definition the kernel cannot check against Erdős's wording is this one:

```lean
def Covers (x y : ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ y → ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ (n : ℤ) ≡ a p [ZMOD p]
```

## Reproducing

**Bridge only (Mathlib, minutes with the Mathlib cache):**

    cd bridge
    lake exe cache get
    lake build

Pinned to Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, the commit used by
`openai/math`. If the cache has no build for that commit, Mathlib compiles from source.

**Against the release (hours: Mathlib plus about 200k lines of the release's Lean):**

    git clone https://github.com/openai/math && cd math
    git checkout fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
    cd lean
    lake update        # fetches dependencies and applies the release's patches
    lake build OAI.NumberTheory.Jacobsthal.Main
    cp <this repo>/erdos-687/glue/JacobsthalTo687.lean .
    lake env lean JacobsthalTo687.lean

Our run: 9,785 build jobs with 0 errors; Mathlib built from source on 2 cores, about 10 hours in total.

**Comparator** (`leanprover/comparator` at `d03acab`, `leanprover/lean4export` at `v4.34.0`, both
built with Lean 4.34.1), from `math/lean`:

    lake env comparator ComparatorChallenges/JacobsthalImproved.json
    lake env comparator ComparatorChallenges/Jacobsthal.json

Caveat: landrun could not be built in our environment, so comparator ran with its bundled
no-sandbox shim (`scripts/fake-landrun.sh`). That removes isolation from build scripts. The
statement comparison, axiom check and kernel replay are unchanged.

## Not covered

- The paper's prose. OpenAI's Lean formalizes the $h(k)$ bound in full; the Lean here only adds the
  reduction.
- The implied constant is ineffective (Siegel–Walfisz in the paper's proof).
- $Y(x) \ll x^{1+o(1)}$, the Maier–Pomerance conjecture $Y(x) \ll x(\log x)^{2+o(1)}$, and Erdős's
  weaker variant allowing $o(y/\log y)$ uncovered integers remain open. The
  Ford–Green–Konyagin–Maynard–Tao lower bound is unchanged.

## References

- P. Erdős, *A survey of problems in combinatorial number theory*, Ann. Discrete Math. 6 (1980), 89–115, §6.
- H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978), 225–231.
- K. Ford, B. Green, S. Konyagin, J. Maynard, T. Tao, *Long gaps between primes*, J. Amer. Math. Soc. 31 (2018), 65–105.
- OpenAI, *A quadratic bound for Jacobsthal's function*, OpenAI Math Release preprint, 25 Sep 2026.
- B. Green, *100 open problems*, Problem 46.

### AI notice

Works produced by HJ van Veen (@30k30), in collaboration with Claude Opus 5.5 extra, ChatGPT Sol 6.1 extra high, and Gemini 3 Pro. 
