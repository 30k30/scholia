import Erdos687.Bridge

open Filter

/-! ## The formal-conjectures statements, exactly as they will appear in the repository

Definitions below are copied verbatim from formal-conjectures (`ErdosProblems/687.lean` and
`GreensOpenProblems/46.lean`); `g ≪ f` there is notation for `Asymptotics.IsBigO atTop g f`,
and `answer(True)` elaborates to `True`. Each statement is proved from the Jacobsthal
hypothesis; the unconditional versions are in the glue file. -/

namespace Erdos687

open Asymptotics

/-- Verbatim from formal-conjectures `ErdosProblems/687.lean`. -/
def IsCoveredByResidues (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 y, ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]

/-- Verbatim from formal-conjectures `ErdosProblems/687.lean`. -/
noncomputable def Y (x : ℕ) : ℝ :=
  ((sSup { y | IsCoveredByResidues x y } : ℕ) : ℝ)

theorem Y_eq_maxY : Y = Green46.maxY := by
  funext x
  rfl

/-- `erdos_687.parts.i`, from the Jacobsthal bound. -/
theorem erdos_687.parts.i_of_jacobsthal (hJ : JacobsthalIteratedLogStatement) :
    True ↔ Y =o[atTop] (fun x : ℕ ↦ (x : ℝ) ^ 2) := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  obtain ⟨h1, h2⟩ := Green46.improve_upper hJ
  rw [Y_eq_maxY]
  exact h2.trans_isLittleO h1

/-- `erdos_687.variants.upper_iterated_log`, from the Jacobsthal bound. -/
theorem erdos_687.variants.upper_iterated_log_of_jacobsthal
    (hJ : JacobsthalIteratedLogStatement) :
    IsBigO atTop Y
      (fun x : ℕ ↦ ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2) := by
  obtain ⟨-, h2⟩ := Green46.improve_upper hJ
  rw [Y_eq_maxY]
  exact h2

end Erdos687

namespace Green46

open Asymptotics

/-- `green_46.improve_upper` with the answer written as it appears in the repository. -/
theorem green_46.improve_upper_of_jacobsthal (hJ : JacobsthalIteratedLogStatement) :
    let ans := ((fun x : ℕ ↦ ((x : ℝ) + 1) ^ 2 /
      (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2) : ℕ → ℝ)
    (ans =o[atTop] bestUpper) ∧ (IsBigO atTop maxY ans) :=
  Green46.improve_upper hJ

end Green46
