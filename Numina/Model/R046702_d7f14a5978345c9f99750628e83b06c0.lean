import Mathlib
open Real Set

theorem algebra_9099 {f : ℝ → ℝ} (hf : f = λ x => logb 2 (x^2 - 4 * x)) :
    MonotoneOn f {x | 4 < x} ∧ AntitoneOn f {x | x < 0} := by 
  constructor
  · -- We need to prove f is Monotone on {x | 4 < x}
    intro x hx y hy hxy
    have h1 : 4 < x := by
      simpa using hx
    have h2 : 4 < y := by
      simpa using hy
    rw [hf]
    have h3 : 0 < x^2 - 4 * x := by
      nlinarith
    have h4 : 0 < y^2 - 4 * y := by
      nlinarith
    have h5 : x^2 - 4 * x ≤ y^2 - 4 * y := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), hxy]
    have h6 : logb 2 (x^2 - 4 * x) ≤ logb 2 (y^2 - 4 * y) := by
      apply Real.logb_le_logb_of_le
      all_goals
        nlinarith
    exact h6
  · -- We need to prove f is Antitone on {x | x < 0}
    intro x hx y hy hxy
    have h1 : x < 0 := by
      simpa using hx
    have h2 : y < 0 := by
      simpa using hy
    rw [hf]
    have h3 : 0 < x^2 - 4 * x := by
      nlinarith
    have h4 : 0 < y^2 - 4 * y := by
      nlinarith
    have h5 : x^2 - 4 * x ≥ y^2 - 4 * y := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), hxy]
    have h6 : logb 2 (x^2 - 4 * x) ≥ logb 2 (y^2 - 4 * y) := by
      apply Real.logb_le_logb_of_le
      all_goals
        nlinarith
    exact h6