import Mathlib

open Real

theorem algebra_323959 (f : ℝ → ℝ) (hf : f = fun x => logb (1 / 3) (x ^ 2 - 5 * x + 6)) :
    MonotoneOn f {x | x < 2} := by
  intro x hx y hy hxy
  have h1 : x < 2 := hx
  have h2 : y < 2 := hy
  have h3 : x ≤ y := hxy
  have h4 : x ^ 2 - 5 * x + 6 ≥ y ^ 2 - 5 * y + 6 := by
    have h5 : x ≤ y := hxy
    have h6 : x < 2 := h1
    have h7 : y < 2 := h2
    have h8 : x - y ≤ 0 := by linarith
    have h9 : x + y - 5 < 0 := by
      have h10 : x < 2 := h1
      have h11 : y < 2 := h2
      nlinarith
    have h10 : (x - y) * (x + y - 5) ≥ 0 := by
      nlinarith
    nlinarith
  have h5 : logb (1 / 3) (x ^ 2 - 5 * x + 6) ≤ logb (1 / 3) (y ^ 2 - 5 * y + 6) := by
    have h6 : x ^ 2 - 5 * x + 6 > 0 := by
      have h7 : x < 2 := h1
      nlinarith
    have h7 : y ^ 2 - 5 * y + 6 > 0 := by
      have h8 : y < 2 := h2
      nlinarith
    have h8 : logb (1 / 3) (x ^ 2 - 5 * x + 6) ≤ logb (1 / 3) (y ^ 2 - 5 * y + 6) := by
      have h9 : logb (1 / 3) (x ^ 2 - 5 * x + 6) = (log (x^2 - 5 * x + 6) ) / (log (1 / 3) ) := by 
        field_simp [logb]
      have h10 : logb (1 / 3) (y ^ 2 - 5 * y + 6) = (log (y ^ 2 - 5 * y + 6) ) / (log (1 / 3) ) := by 
        field_simp [logb]
      rw [h9, h10]
      have h11 : log (1 / 3) < 0 := by
        have h12 : log (1 / 3) < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals norm_num
        have h13 : log (1 : ℝ) = 0 := by
          rw [log_one]
        linarith
      have h12 : log (x ^ 2 - 5 * x + 6) ≥ log (y ^ 2 - 5 * y + 6) := by
        have h13 : x ^ 2 - 5 * x + 6 ≥ y ^ 2 - 5 * y + 6 := by
          nlinarith
        have h14 : x ^ 2 - 5 * x + 6 > 0 := h6
        have h15 : y ^ 2 - 5 * y + 6 > 0 := h7
        apply Real.log_le_log
        all_goals linarith
      have h13 : (log (x ^ 2 - 5 * x + 6) ) / (log (1 / 3) ) ≤ (log (y ^ 2 - 5 * y + 6) ) / (log (1 / 3) ) := by
        apply (div_le_div_right_of_neg h11).mpr
        linarith
      linarith
    linarith
  have h6 : f x = logb (1 / 3) (x ^ 2 - 5 * x + 6) := by 
    rw [hf]
  have h7 : f y = logb (1 / 3) (y ^ 2 - 5 * y + 6) := by 
    rw [hf]
  rw [h6, h7]
  linarith [h5]