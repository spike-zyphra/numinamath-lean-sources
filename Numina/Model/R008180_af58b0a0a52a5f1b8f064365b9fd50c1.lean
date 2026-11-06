import Mathlib
open Real Set

theorem algebra_9095 {f : ℝ → ℝ} (hf : f = λ x => logb 2 (x^2 + x)) :
    StrictMonoOn f (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h1 : 0 < x := hx
  have h2 : 0 < y := hy
  have h3 : x < y := hxy
  have h4 : x ^ 2 + x < y ^ 2 + y := by
    nlinarith [sq_nonneg (x - y), sq_pos_of_pos h1, sq_pos_of_pos h2]
  rw [hf]
  have h5 : x ^ 2 + x > 0 := by
    nlinarith [sq_pos_of_pos h1]
  have h6 : y ^ 2 + y > 0 := by
    nlinarith [sq_pos_of_pos h2]
  have h7 : logb 2 (x ^ 2 + x) < logb 2 (y ^ 2 + y) := by
    apply Real.logb_lt_logb
    all_goals nlinarith [h5, h6, h4]
  exact h7