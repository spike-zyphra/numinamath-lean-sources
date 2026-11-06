import Mathlib

theorem algebra_83696 (n : ℕ) (hn : n > 0) (x y : ℝ)
    (hx : x = (Real.sqrt (n + 2) - Real.sqrt n) / (Real.sqrt (n + 2) + Real.sqrt n))
    (hy : y = (Real.sqrt (n + 2) + Real.sqrt n) / (Real.sqrt (n + 2) - Real.sqrt n))
    (h : 14 * x ^ 2 + 26 * x * y + 14 * y ^ 2 = 2014) : n = 5 := by

  have hxy1 : x * y = 1 := by
    rw [hx, hy]
    have h1 : Real.sqrt (n + 2) + Real.sqrt n ≠ 0 := by
      have h2 : Real.sqrt (n + 2) > 0 := by
        have h4 : (n + 2 : ℝ) > 0 := by
          have hn2 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast (show n > 0 by linarith)
          nlinarith
        positivity
      have h5 : Real.sqrt (n : ℝ) ≥ 0 := by positivity
      linarith
    have h1' : Real.sqrt (n + 2) - Real.sqrt n ≠ 0 := by
      by_contra h6
      have h7 : Real.sqrt (n + 2) = Real.sqrt n := by linarith
      have h8 : (n + 2 : ℝ) = (n : ℝ) := by
        rw [Real.sqrt_inj (by positivity) (by positivity) ] at h7
        nlinarith
      nlinarith
    field_simp [h1', h1]
    <;> nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 2 : ℝ) by positivity)]

  have h2 : x ^ 2 + y ^ 2 = 142 := by
    have h' : 14 * (x ^ 2 + y ^ 2) + 26 * (x * y) = 2014 := by
      nlinarith
    rw [show x * y = 1 by nlinarith [hxy1]] at h'
    linarith

  have eq2 : x + y = 12 := by
    have h3 : (x + y) ^ 2 = 144 := by
      calc
        (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by ring
        _ = (142) + 2 * (1) := by rw [h2, hxy1]
        _ = 144 := by norm_num
    have h4 : x + y > 0 := by
      rw [hx, hy]
      have h5 : Real.sqrt (n + 2) + Real.sqrt n > 0 := by
        have h51 : Real.sqrt (n + 2) > 0 := by
          have h41 : (n + 2 : ℝ) > 0 := by
            have hn2 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast (show n > 0 by linarith)
            nlinarith
          positivity
        have h61 : Real.sqrt (n : ℝ) ≥ 0 := by positivity
        linarith
      have h5' : Real.sqrt (n + 2) - Real.sqrt n > 0 := by
        have h11 : Real.sqrt (n + 2) > Real.sqrt n := by
          have h21 : (n + 2 : ℝ) > (n : ℝ) := by
            have hn2 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast (show n > 0 by linarith)
            nlinarith
          have h31 : Real.sqrt (n + 2) > Real.sqrt (n) := by
            apply Real.sqrt_lt_sqrt
            all_goals linarith
          linarith
        nlinarith
      have h51 : (Real.sqrt (n + 2) - Real.sqrt n) + (Real.sqrt (n + 2) + Real.sqrt n) > 0 := by
        linarith
      positivity
    have h5 : x + y = 12 := by nlinarith
    linarith

  rw [hx, hy] at eq2
  have eq3 : Real.sqrt (n) ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have eq4 : Real.sqrt (n + 2) ^ 2 = (n + 2 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have h8 : (Real.sqrt (n + 2) )^ 2 - Real.sqrt n ^ 2 = 2 := by
    nlinarith

  field_simp [(show Real.sqrt (n + 2) - Real.sqrt n ≠ 0 by
    by_contra h0
    have h11 : Real.sqrt (n + 2) = Real.sqrt n := by nlinarith
    have h41 : (n + 2 : ℝ) = (n : ℝ) := by
      rw [Real.sqrt_inj (by positivity) (by positivity)] at h11
      nlinarith
    nlinarith
  ), (show Real.sqrt (n + 2) + Real.sqrt n ≠ 0 by
    have h1 : Real.sqrt (n + 2) + Real.sqrt n > 0 := by
      have h2 : Real.sqrt (n + 2) > 0 := by
        have h4 : (n + 2 : ℝ) > 0 := by
          have hn2 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast (show n > 0 by linarith)
          nlinarith
        positivity
      have h3 : Real.sqrt (n : ℝ) ≥ 0 := by positivity
      linarith
    linarith
  )] at eq2
  have hn1 : (n : ℝ) > 0 := by positivity
  have h100 : (n : ℝ) = 5 := by
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 2 : ℝ)]
  exact_mod_cast h100