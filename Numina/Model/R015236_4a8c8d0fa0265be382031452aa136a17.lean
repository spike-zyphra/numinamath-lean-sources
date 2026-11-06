import Mathlib

open Real Set
open scoped BigOperators

/- Given $a<{}0$, and $|a|x\leqslant a$, then the minimum value of $|2x-6|-|x-2|$ is ___          ___. -/
theorem inequalities_2723 (a : ℝ) (ha : a < 0) (x : ℝ) (hx : abs a * x ≤ a) :
    abs (2 * x - 6) - abs (x - 2) ≥ 5 := by
  have h1 : abs a = -a := by
    rw [abs_of_neg ha]
  
  rw [h1] at hx
  have h2 : x ≤ -1 := by
    nlinarith [ha]

  have h3 : abs (2 * x - 6) = 6 - 2 * x := by
    have h4 : 2 * x - 6 < 0 := by
      nlinarith [h2]
    rw [abs_of_neg h4]
    all_goals linarith

  have h4 : abs (x - 2) = 2 - x := by
    have h5 : x - 2 < 0 := by
      nlinarith [h2]
    rw [abs_of_neg h5]
    all_goals linarith
  have h5 : abs (2 * x - 6) - abs (x - 2) = 4 - x := by
    rw [h3, h4]
    all_goals linarith
  have h6 : 4 - x ≥ 5 := by
    linarith [h2]
  linarith [h5, h6]