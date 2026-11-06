import Mathlib

open Real

theorem algebra_2462 {n : ℕ} (hn : 0 < n) (x y : ℝ)
    (hx : x = (sqrt (n + 1) - sqrt n) / (sqrt (n + 1) + sqrt n))
    (hy : y = (sqrt (n + 1) + sqrt n) / (sqrt (n + 1) - sqrt n))
    (h : 2 * x ^ 2 + 197 * x * y + 2 * y ^ 2 = 1993) :
    n = 7 := by
  have h1 : sqrt (n : ℝ) > 0 := by
    have hn' : (n : ℝ) > 0 := by
      exact_mod_cast (show (n : ℕ) > 0 by linarith)
    exact Real.sqrt_pos.2 hn'
  have h2 : sqrt ((n + 1 : ℝ) ) > 0 := by
    have hn' : (n + 1 : ℝ) > 0 := by
      have hn1 : (n : ℕ) > 0 := hn
      have : (n + 1 : ℕ) > 0 := by linarith
      exact_mod_cast (show (n + 1 : ℕ) > 0 by linarith)
    exact Real.sqrt_pos.2 hn'
  have hxy : x * y = 1 := by
    rw [hx, hy]
    have h3 : sqrt (n + 1 : ℝ) + sqrt (n : ℝ) ≠ 0 := by
      linarith [h1, h2]
    have h4 : sqrt (n + 1 : ℝ) - sqrt (n : ℝ) ≠ 0 := by
      by_contra h'
      have h5 : sqrt (n + 1 : ℝ) = sqrt (n : ℝ) := by linarith [h']
      have h6 : (n + 1 : ℝ) = (n : ℝ) := by
        rw [Real.sqrt_inj (by positivity) (by positivity) ] at h5
        linarith [h5]
      have h7 : (1 : ℝ) = 0 := by
        nlinarith
      linarith
    field_simp [h3, h4]
    <;> nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), sq_pos_of_pos h1, sq_pos_of_pos h2, mul_pos h1 h2]
  have h_eq1 : 2 * x ^ 2 + 2 * y ^ 2 = 1796 := by
    nlinarith [h, hxy]
  have h_eq2 : x + y = 4 * (n : ℝ) + 2 := by
    have eq1 : x = (sqrt (n + 1 : ℝ) - sqrt (n : ℝ) ) ^ 2 := by
      rw [hx]
      have h3 : sqrt (n + 1 : ℝ) + sqrt (n : ℝ) ≠ 0 := by
        linarith [h1, h2]
      field_simp [h3]
      <;> nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), sq_pos_of_pos h1, sq_pos_of_pos h2, mul_pos h1 h2]
    have eq2 : y = (sqrt (n + 1 : ℝ) + sqrt (n : ℝ) ) ^ 2 := by
      rw [hy]
      have h3 : sqrt (n + 1 : ℝ) - sqrt (n : ℝ) ≠ 0 := by
        by_contra h'
        have h5 : sqrt (n + 1 : ℝ) = sqrt (n : ℝ) := by linarith [h']
        have h6 : (n + 1 : ℝ) = (n : ℝ) := by
          rw [Real.sqrt_inj (by positivity) (by positivity) ] at h5
          linarith [h5]
        have h7 : (1 : ℝ) = 0 := by
          nlinarith
        linarith
      field_simp [h3]
      <;> nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), sq_pos_of_pos h1, sq_pos_of_pos h2, mul_pos h1 h2]
    rw [eq1, eq2]
    nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), sq_pos_of_pos h1, sq_pos_of_pos h2, mul_pos h1 h2]
  have h_eq3 : (x + y) ^ 2 = 900 := by
    nlinarith [h_eq1, hxy]
  have h_eq4 : x + y = 30 := by
    have h3 : x + y > 0 := by
      nlinarith [h_eq2, show (n : ℝ) > (0 : ℝ) by positivity]
    nlinarith [h_eq3, h3]
  have h_eq5 : (4 * (n : ℝ) + 2) = 30 := by
    linarith [h_eq2, h_eq4]
  have h_eq6 : (n : ℝ) = 7 := by
    nlinarith [h_eq5]
  have h_eq7 : n = 7 := by
    exact_mod_cast h_eq6
  exact h_eq7