import Mathlib

open Real

theorem inequalities_112268 (a : ℝ) (ha : 0 ≤ a) :
    ∀ x : ℝ, abs (x - a) + abs (x + a) ≥ 2 * a := by 
  intro x
  by_cases h1 : x ≥ a
  · -- Case x ≥ a
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [show a ≤ x from by linarith])]
    linarith
  · -- Case x < a
    by_cases h2 : x ≤ -a
    · -- Case x ≤ -a
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [show x ≤ -a from by linarith])]
      linarith
    · -- Case -a < x < a
      rw [abs_of_nonpos (show x - a ≤ 0 by linarith), abs_of_nonneg (show x + a ≥ 0 by linarith [show -a ≤ x from by linarith])]
      all_goals linarith