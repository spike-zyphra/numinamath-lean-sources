import Mathlib

open Real

theorem algebra_182704 {k : ℝ} (hk : ∃ x y, x > 0 ∧ y > 0 ∧ logb 5 x = k ∧ logb 5 (x + 4) = k - 0.5) :
    k = 6 + sqrt 10 := by
  rcases hk with ⟨x, y, hx1, hy1, h1, h2⟩
  have h3 : x > 0 := hx1
  have h4 : x = (5 : ℝ) ^ k := by
    have h5 : x = (5 : ℝ) ^ (logb 5 x) := by
      field_simp [Real.rpow_logb, hx1]
      all_goals linarith
    rw [h1] at h5
    exact h5
  have h6 : x + 4 = (5 : ℝ) ^ (k - 0.5 : ℝ) := by
    have h7 : x + 4 = (5 : ℝ) ^ (logb 5 (x + 4)) := by
      field_simp [Real.rpow_logb, show x + 4 > 0 by linarith]
      all_goals linarith
    rw [h2] at h7
    exact h7
  exfalso
  have eq3 : (5 : ℝ) ^ k = (5 : ℝ) ^ (k - 0.5 : ℝ) - 4 := by
    have kg : (5 : ℝ) ^ k = x := by linarith [h4]
    have hg : (5 : ℝ) ^ (k - 0.5 : ℝ) = x + 4 := by linarith [h6]
    nlinarith [hg, kg]
  have h7 : k > k - 0.5 := by
    nlinarith
  -- Now we need to show that 5^k < 5^(k - 0.5) from eq3
  -- However let's try to use `nlinarith` with exp
  have h8 : (5 : ℝ) ^ k > (5 : ℝ) ^ (k - 0.5 : ℝ) := by
    have h11 : (5 : ℝ) ^ k > (5 : ℝ) ^ (k - 0.5 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals
        try linarith
        try norm_num
    linarith [h11]
  -- Now the contradiction shows between eq3 and h8
  -- From eq3
  -- 5^k = 5^(k - 0.5) - 4
  -- 5^k + 4 = 5^(k - 0.5)
  -- Since 4 > 0, it would be that 5^k < 5^(k - 0.5)
  -- but h8 tells it's the opposite, so indeed a contradiction.
  nlinarith [eq3, h8]