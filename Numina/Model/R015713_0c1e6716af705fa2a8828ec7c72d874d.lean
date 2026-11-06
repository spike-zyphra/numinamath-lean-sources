import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_323140 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (-x^2 - 2*x + 3)) :
    StrictMonoOn f (Ico (-1) 1) := by
  intros x hx y hy hxy
  have h1 : -1 ≤ x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : -1 ≤ y := hy.1
  have h4 : y < 1 := hy.2
  have h5 : x < y := hxy
  have h6 : -x ^ 2 - 2 * x + 3 > 0 := by
    nlinarith
  have h7 : -y ^ 2 - 2 * y + 3 > 0 := by
    nlinarith
  have h8 : -x ^ 2 - 2 * x + 3 > -y ^ 2 - 2 * y + 3 := by
    have h9 : x < y := h5
    have h10 : x ≥ -1 := by linarith
    have h11 : y ≤ 1 := by linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  have h9 : f x < f y := by
    rw [hf]
    have h10 : logb (1 / 2) (-x ^ 2 - 2 * x + 3) < logb (1 / 2) (-y ^ 2 - 2 * y + 3) := by
      apply Real.logb_lt_logb_of_base_lt_one
      all_goals
        try { norm_num }
        try { nlinarith }
    simpa using h10
  exact h9