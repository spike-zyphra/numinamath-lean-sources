import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_322103 {f : ℝ → ℝ} (hf : f = λ x => logb 0.5 (x^2 + 4 * x + 4)) :
    StrictMonoOn f {x | x < -2} := by
  intro x hx y hy hxy
  have h1 : x < -2 := hx
  have h2 : y < -2 := hy
  have h3 : x < y := hxy
  have h4 : x ^ 2 + 4 * x + 4 > 0 := by
    have h5 : x < -2 := hx
    nlinarith
  have h5 : y ^ 2 + 4 * y + 4 > 0 := by
    have h6 : y < -2 := hy
    nlinarith
  rw [hf]
  have h6 : x ^ 2 + 4 * x + 4 > y ^ 2 + 4 * y + 4 := by
    have h7 : x < y := hxy
    have h8 : x < -2 := hx
    have h9 : y < -2 := hy
    nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2)]
  have h7 : logb (0.5 : ℝ) (x^2 + 4 * x + 4) < logb (0.5 : ℝ) (y^2 + 4 * y + 4) := by
    have h8 : (0.5 : ℝ) < 1 := by norm_num
    have h9 : (0.5 : ℝ) > 0 := by norm_num
    have h10 : x ^ 2 + 4 * x + 4 > y ^ 2 + 4 * y + 4 := h6
    have h11 : logb (0.5 : ℝ) (x ^ 2 + 4 * x + 4) < logb (0.5 : ℝ) (y ^ 2 + 4 * y + 4) := by
      apply Real.logb_lt_logb_of_base_lt_one
      all_goals
        try { norm_num }
        all_goals
          nlinarith [h4, h5, h6]
    linarith
  apply h7