import Mathlib

theorem algebra_217837 {x : ℝ} (hx : x > 0) (h : 90 / x = (1 - 1.5) * (90 / (x + 4))) :
    x = 10 := by 
  have h1 : x + 4 ≠ 0 := by
    nlinarith

  have h2 : 90 / x > 0 := by
    apply div_pos
    norm_num
    all_goals linarith

  have h3 : (1 - 1.5 : ℝ) * (90 / (x + 4)) < 0 := by
    have h4 : (x + 4) > 0 := by
      nlinarith
    have h5 : (90 / (x + 4)) > 0 := by
      apply div_pos
      norm_num
      all_goals nlinarith
    have h7 : (1 - 1.5 : ℝ) < 0 := by norm_num
    nlinarith

  -- The equality h states 90 / x equals a negative number
  -- But 90 / x > 0
  -- So this is a contradiction
  linarith [h, h2, h3]