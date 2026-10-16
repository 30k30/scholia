import Erdos687.Bridge

open Filter

/-! ## The formal-conjectures statements, exactly as they appear in the repository

Definitions below are copied verbatim from formal-conjectures: `GreensOpenProblems/46.lean`
(as updated in PR #7183, using the repository's `<theorem>.answer` convention) and
`ErdosProblems/687.lean` (as in PR #6864, by Daniel Veljjanoski). There `g ≪ f` is notation for
`Asymptotics.IsBigO atTop g f`. Each statement is proved from the Jacobsthal hypothesis; the
unconditional versions are in the glue file. -/

namespace Green46

open Asymptotics

/-- Verbatim from formal-conjectures `GreensOpenProblems/46.lean` (PR #7183). -/
noncomputable def green_46.improve_upper.answer : ℕ → ℝ :=
  fun x : ℕ ↦ ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2

/-- `green_46.improve_upper`, from the Jacobsthal bound. -/
theorem green_46.improve_upper_of_jacobsthal (hJ : JacobsthalIteratedLogStatement) :
    (green_46.improve_upper.answer =o[atTop] bestUpper) ∧
      (IsBigO atTop maxY green_46.improve_upper.answer) := by
  obtain ⟨h1, h2⟩ := Green46.improve_upper hJ
  exact ⟨h1, h2⟩

end Green46

namespace Erdos687

open Asymptotics

/-- Verbatim from formal-conjectures `ErdosProblems/687.lean` (PR #6864). -/
noncomputable def Y (x : ℕ) : ℕ :=
  sSup {y : ℕ | Green46.IsCoveredByResidues x y}

/-- `erdos_687.parts.ii` of PR #6864, from the Jacobsthal bound. -/
theorem erdos_687.parts.ii_of_jacobsthal (hJ : JacobsthalIteratedLogStatement) :
    (fun x : ℕ ↦ (Y x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ) ^ 2) := by
  obtain ⟨h1, h2⟩ := Green46.improve_upper hJ
  exact h2.trans_isLittleO h1

end Erdos687
