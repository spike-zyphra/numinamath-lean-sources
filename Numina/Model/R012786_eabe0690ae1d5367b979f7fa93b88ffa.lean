import Mathlib

theorem number_theory_96464 : Irrational (Real.sqrt 2) ∧ ¬∃ (x : ℚ), Real.sqrt 2 = x := by
  constructor
  · -- Show that $\sqrt{2}$ is irrational
    native_decide
  · -- Show that there does not exist a rational number $x$ such that $\sqrt{2} = x$
    rintro ⟨x, hx⟩
    have h1 : Irrational (Real.sqrt 2) := by
      native_decide
    -- We have a contradiction because $\sqrt{2}$ is irrational
    -- but (x : ℚ) is rational
    have h3 : ¬ Irrational (Real.sqrt 2) := by
      rw [show Real.sqrt 2 = (x : ℝ) by linarith [hx]]
      simp [Rat.not_irrational]
    contradiction