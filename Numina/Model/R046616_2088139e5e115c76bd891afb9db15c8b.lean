import Mathlib
open Real

/- Define a function $f$ as follows, which is needed for the problem statement -/
def f  (x : ℝ) := (x^2 + 6*x + 2)^2

theorem algebra_609160 : (∀x, (f x) ≥ 0) ∧ (f (-3+sqrt 7) = 0) ∧ (f (-3+sqrt 7) = 0) := by
  constructor
  · -- Show that $f(x) \geq 0$ for all real numbers $x$.
    intro x
    dsimp [f]
    positivity
  constructor
  · -- Show that f(-3 + sqrt 7) = 0.
    dsimp [f]
    have h1 : ((-3 + Real.sqrt 7 : ℝ) ^ 2 + 6 * (-3 + Real.sqrt 7 : ℝ) + 2) = (0 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
    rw [h1]
    all_goals norm_num
  · -- Show that f(-3 + sqrt 7) = 0.
    dsimp [f]
    have h1 : ((-3 + Real.sqrt 7 : ℝ) ^ 2 + 6 * (-3 + Real.sqrt 7 : ℝ) + 2) = (0 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
    rw [h1]
    all_goals norm_num