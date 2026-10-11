import OAI.NumberTheory.Jacobsthal.Main

/-!
# From Jacobsthal's function to Erdős 687 / Green 46

This file uses only Mathlib. It proves that the improved Jacobsthal bound
`h(k) ≤ C k^2 / (log log 3k)^2` (stated literally as `JacobsthalIteratedLogStatement`, in the
exact form of the comparator challenge `ComparatorChallenges/JacobsthalImproved.lean` of the
OpenAI math release, item 021) implies:

* Erdős Problem 687, the `o(x^2)` question: no choice of one residue class per prime `p ≤ x`
  covers `[1, y]` with `y > ε x^2`, for any fixed `ε > 0` and all large `x`;
* Ben Green's Open Problem 46, `green_46.improve_upper`, against the definitions of
  DeepMind's formal-conjectures repository (copied verbatim below).

It also checks that the quadratic bound implies the right-hand side of formal-conjectures'
`erdos_970`. The step from Jacobsthal's function to Erdős 687 is the Chinese remainder theorem:
`Y(x) = j(x#) - 1` (cf. Ford–Green–Konyagin–Maynard–Tao, *Long gaps between primes*, (1.3)).
-/

open Filter
open scoped Function

/-- The improved Jacobsthal bound, written out with no auxiliary definitions. -/
def JacobsthalIteratedLogStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ,
      (∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
        ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n) ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2

/-- The quadratic Jacobsthal bound, written out with no auxiliary definitions. -/
def JacobsthalQuadraticStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ,
      (∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
        ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n) ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2

/-! ## The formal-conjectures statement of Erdős 970 -/

namespace FC970

/-- Verbatim from formal-conjectures `ErdosProblems/970.lean`. -/
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/-- Verbatim from formal-conjectures `ErdosProblems/970.lean`. -/
noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}

/-- The right-hand side of formal-conjectures' `erdos_970`, so its `answer` is `True`. -/
theorem erdos_970_rhs (hJ : JacobsthalQuadraticStatement) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  obtain ⟨C, hC, h⟩ := hJ
  refine ⟨C, hC, fun k hk => ?_⟩
  obtain ⟨m, hm, hmC⟩ := h k hk
  have h1 : jacobsthalFunction k ≤ m := Nat.sInf_le (show IsJacobsthalBound k m from hm)
  have h2 : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast h1
  linarith

end FC970

/-! ## Erdős 687 -/

namespace Erdos687

/-- Erdős 687's covering condition: every integer in `[1, y]` lies in the chosen class `a p`
modulo some prime `p ≤ x`. `Y(x)` is the largest `y` for which some `a` works. -/
def Covers (x y : ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ y → ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ (n : ℤ) ≡ a p [ZMOD p]

/-- The Chinese remainder step: a covering of `[1, y]` by one class for each prime `≤ x`
produces `y` consecutive integers, each sharing a prime factor with `x#`. So `y` is smaller
than any interval length `m` that is guaranteed to contain an integer coprime to `x#`. -/
theorem lt_of_covers {x y m : ℕ} {a : ℕ → ℤ} (hcov : Covers x y a)
    (hm : ∀ a' : ℤ, ∃ i : ℕ, i < m ∧ (a' + i).natAbs.Coprime (primorial x)) : y < m := by
  by_contra! hym
  have hs : ∀ p ∈ Nat.primesLE x, id p ≠ 0 :=
    fun p hp => (Nat.prime_of_mem_primesLE hp).ne_zero
  have pp : Set.Pairwise (Nat.primesLE x : Set ℕ) (Nat.Coprime on id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE hp)
      (Nat.prime_of_mem_primesLE hq)).2 hpq
  obtain ⟨A, hA⟩ :=
    Nat.chineseRemainderOfFinset (fun p => ((a p) % (p : ℤ)).toNat) id (Nat.primesLE x) hs pp
  obtain ⟨i, hi, hcop⟩ := hm (1 - (A : ℤ))
  obtain ⟨p, hp, hpx, hcong⟩ := hcov (i + 1) (by omega) (by omega)
  have hpS : p ∈ Nat.primesLE x := Nat.mem_primesLE.2 ⟨hpx, hp⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAp : A ≡ ((a p) % (p : ℤ)).toNat [MOD p] := hA p hpS
  have h1 : (A : ℤ) ≡ a p [ZMOD p] := by
    have h := (Int.natCast_modEq_iff).2 hAp
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)] at h
    exact h.trans (Int.mod_modEq _ _)
  have h2 : (A : ℤ) ≡ ((i + 1 : ℕ) : ℤ) [ZMOD p] := h1.trans hcong.symm
  have h3 : (p : ℤ) ∣ 1 - (A : ℤ) + (i : ℤ) := by
    have h := h2.dvd
    have e : ((i + 1 : ℕ) : ℤ) - (A : ℤ) = 1 - (A : ℤ) + (i : ℤ) := by push_cast; ring
    rwa [e] at h
  have h4 : p ∣ (1 - (A : ℤ) + (i : ℤ)).natAbs := Int.natCast_dvd.1 h3
  have h5 : p ∣ primorial x := hp.dvd_primorial_iff.2 hpx
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h4 h5)

/-- Explicit form: `Y(x) < C (x+1)^2 / (log log (3(x+1)))^2` for every `x`, with the constant
of the improved Jacobsthal bound, applied with `k = x + 1`. -/
theorem explicit (hJ : JacobsthalIteratedLogStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, ∀ a : ℕ → ℤ, Covers x y a →
      (y : ℝ) < C * ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2 := by
  obtain ⟨C, hC, hmain⟩ := hJ
  refine ⟨C, hC, fun x y a hcov => ?_⟩
  obtain ⟨m, hJm, hmC⟩ := hmain (x + 1) (Nat.succ_pos x)
  have hcard : (primorial x).primeFactors.card ≤ x + 1 := by
    rw [primeFactors_primorial, Nat.primesLE_eq_filter_range]
    exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  have hym : y < m := lt_of_covers hcov (hJm (primorial x) (primorial_pos x) hcard)
  have hym' : (y : ℝ) < m := by exact_mod_cast hym
  push_cast at hmC
  linarith

theorem tendsto_loglog :
    Tendsto (fun x : ℕ => Real.log (Real.log (3 * ((x : ℝ) + 1)))) atTop atTop := by
  have h1 : Tendsto (fun x : ℕ => 3 * ((x : ℝ) + 1)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)

/-- Eventually `C (x+1)^2 / (log log 3(x+1))^2 ≤ ε x^2`. -/
theorem eventually_le (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      C * ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2
        ≤ ε * (x : ℝ) ^ 2 := by
  filter_upwards [tendsto_loglog.eventually_ge_atTop (4 * C / ε + 1), eventually_ge_atTop 1]
    with x hx hx1
  set L := Real.log (Real.log (3 * ((x : ℝ) + 1))) with hLdef
  have hq : (0 : ℝ) ≤ 4 * C / ε := div_nonneg (by linarith) hε.le
  have hL1 : 1 ≤ L := by linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have key : 4 * C ≤ ε * L := by
    have h := mul_le_mul_of_nonneg_left hx hε.le
    have e : ε * (4 * C / ε + 1) = 4 * C + ε := by
      rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hε.ne', mul_one]
    linarith
  have key2 : 4 * C ≤ ε * L ^ 2 := by nlinarith
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hL2 : 0 < L ^ 2 := by positivity
  rw [div_le_iff₀ hL2]
  have hsq : ((x : ℝ) + 1) ^ 2 ≤ 4 * (x : ℝ) ^ 2 := by nlinarith
  have h1 : C * ((x : ℝ) + 1) ^ 2 ≤ 4 * C * (x : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hC.le
    linarith
  have h2 : 4 * C * (x : ℝ) ^ 2 ≤ ε * L ^ 2 * (x : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right key2 (sq_nonneg _)
  nlinarith

/-- Erdős 687's question "can one prove `Y(x) = o(x^2)`?": for every `ε > 0`, for all large `x`,
no choice of one class per prime `p ≤ x` covers `[1, y]` with `y > ε x^2`. -/
theorem little_o (hJ : JacobsthalIteratedLogStatement) :
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∀ y : ℕ, ∀ a : ℕ → ℤ, Covers x y a →
      (y : ℝ) ≤ ε * (x : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hexp⟩ := explicit hJ
  filter_upwards [eventually_le C ε hC hε] with x hx y a hcov
  exact (hexp x y a hcov).le.trans hx

end Erdos687

/-! ## Ben Green's Open Problem 46 (the same question), as formalized in formal-conjectures

Definitions copied verbatim from `FormalConjectures/GreensOpenProblems/46.lean`; there `g ≪ f`
is notation for `Asymptotics.IsBigO atTop g f`, written out here. -/

namespace Green46

open Asymptotics

def IsCoveredByResidues (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 y, ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]

noncomputable def maxY (x : ℕ) : ℝ :=
  ((sSup { y | IsCoveredByResidues x y } : ℕ) : ℝ)

noncomputable def bestUpper (x : ℕ) : ℝ := (x : ℝ) ^ 2

/-- The witness for `answer(sorry)` in `green_46.improve_upper`. -/
noncomputable def ans (x : ℕ) : ℝ :=
  ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2

theorem covers_of_isCovered {x y : ℕ} (h : IsCoveredByResidues x y) :
    ∃ a : ℕ → ℤ, Erdos687.Covers x y a := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun p => (a p : ℤ), fun n hn1 hny => ?_⟩
  obtain ⟨p, hpx, hp, hmod⟩ := ha n (Finset.mem_Icc.2 ⟨hn1, hny⟩)
  exact ⟨p, hp, hpx, (Int.natCast_modEq_iff).2 hmod⟩

theorem maxY_lt (hJ : JacobsthalIteratedLogStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, maxY x < C * ans x := by
  obtain ⟨C, hC, hexp⟩ := Erdos687.explicit hJ
  refine ⟨C, hC, fun x => ?_⟩
  have hbound : ∀ y : ℕ, IsCoveredByResidues x y → (y : ℝ) < C * ans x := by
    intro y hy
    obtain ⟨a, ha⟩ := covers_of_isCovered hy
    have := hexp x y a ha
    simpa only [ans, mul_div_assoc] using this
  have h0 : IsCoveredByResidues x 0 := ⟨fun _ => 0, fun m hm => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
    exact (by omega : False).elim⟩
  have hne : ({ y | IsCoveredByResidues x y } : Set ℕ).Nonempty := ⟨0, h0⟩
  have hbdd : BddAbove ({ y | IsCoveredByResidues x y } : Set ℕ) :=
    bddAbove_def.2 ⟨⌈C * ans x⌉₊, fun y hy => (Nat.lt_ceil.2 (hbound y hy)).le⟩
  exact hbound _ (Nat.sSup_mem hne hbdd)

theorem ans_isLittleO : ans =o[atTop] bestUpper := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [Erdos687.eventually_le 1 c one_pos hc] with x hx
  have hans : 0 ≤ ans x := by unfold ans; positivity
  rw [Real.norm_of_nonneg hans,
    Real.norm_of_nonneg (show (0 : ℝ) ≤ bestUpper x by unfold bestUpper; positivity)]
  simpa only [ans, bestUpper, one_mul] using hx

/-- `green_46.improve_upper` with `answer := ans`: its conclusion, verbatim up to unfolding `≪`. -/
theorem improve_upper (hJ : JacobsthalIteratedLogStatement) :
    let ans' := (ans : ℕ → ℝ)
    (ans' =o[atTop] bestUpper) ∧ (IsBigO atTop maxY ans') := by
  intro ans'
  refine ⟨ans_isLittleO, ?_⟩
  obtain ⟨C, hC, h⟩ := maxY_lt hJ
  refine IsBigO.of_bound C (Eventually.of_forall fun x => ?_)
  have hmax : 0 ≤ maxY x := by unfold maxY; positivity
  have hans : 0 ≤ ans x := by unfold ans; positivity
  rw [Real.norm_of_nonneg hmax, Real.norm_of_nonneg hans]
  exact (h x).le

end Green46

/-! ## Instantiation with the OpenAI release's formal proofs

`OAI.Erdos970.Erdos970Final.erdos_970_iterated_log` and `erdos_970_quadratic` are the
comparator-checked theorems of `lean/OAI/NumberTheory/Jacobsthal` in github.com/openai/math.
Their statements are restated here with no repository definitions, so these terms typecheck
only if the release proves exactly the stated bounds. -/

theorem jacobsthal_iterated_log : JacobsthalIteratedLogStatement :=
  OAI.Erdos970.Erdos970Final.erdos_970_iterated_log

theorem jacobsthal_quadratic : JacobsthalQuadraticStatement :=
  OAI.Erdos970.Erdos970Final.erdos_970_quadratic

/-- Erdős 970 (formal-conjectures form): `h(k) ≪ k^2`. -/
theorem erdos_970_solved :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (FC970.jacobsthalFunction k : ℝ) ≤ C * k ^ 2 :=
  FC970.erdos_970_rhs jacobsthal_quadratic

/-- Erdős 687: `Y(x) = o(x^2)`. -/
theorem erdos_687_little_o :
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∀ y : ℕ, ∀ a : ℕ → ℤ, Erdos687.Covers x y a →
      (y : ℝ) ≤ ε * (x : ℝ) ^ 2 :=
  Erdos687.little_o jacobsthal_iterated_log

/-- Green 46, `improve_upper`, with `answer := (x+1)^2 / (log log 3(x+1))^2`. -/
theorem green_46_improve_upper :
    (Green46.ans =o[atTop] Green46.bestUpper) ∧
      Asymptotics.IsBigO atTop Green46.maxY Green46.ans :=
  Green46.improve_upper jacobsthal_iterated_log

#print axioms erdos_970_solved
#print axioms erdos_687_little_o
#print axioms green_46_improve_upper
