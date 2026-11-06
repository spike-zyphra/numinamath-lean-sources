import Mathlib

theorem inequalities_296660 (p q r : ℝ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0)
    (h : p * q * r = 1) (n : ℕ) (hn : n > 0) :
    1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) +
    1 / (r ^ n + p ^ n + 1) ≤ 1 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : 0 < p ^ n := by positivity
  have h2 : 0 < q ^ n := by positivity
  have h3 : 0 < r ^ n := by positivity
  have h4 : 0 < p ^ n + q ^ n + 1 := by positivity
  have h5 : 0 < q ^ n + r ^ n + 1 := by positivity
  have h6 : 0 < r ^ n + p ^ n + 1 := by positivity
  have h7 : 1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1 ≤ 0 := by
    have h9 : 0 < (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) := by positivity
    have eq1 : 1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1 =
        ( (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ) / ( (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ) := by
      field_simp
      ring
    rw [eq1] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is non-positive
      have eq2 : (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ≤ 0 := by
        have h10 : p ^ n * q ^ n * r ^ n = 1 := by
          have h8 : p ^ n * q ^ n * r ^ n = (p * q * r) ^ n := by
            rw [mul_pow, mul_pow]
            <;> ring
          rw [h8, h]
          <;> norm_num
        nlinarith [sq_nonneg (p ^ n - q ^ n), sq_nonneg (q ^ n - r ^ n), sq_nonneg (r ^ n - p ^ n), 
          sq_nonneg (p ^ n * q ^ n - 1), sq_nonneg (q ^ n * r ^ n - 1), sq_nonneg (r ^ n * p ^ n - 1), 
          h10, 
            mul_nonneg (show (0 : ℝ) ≤ p ^ n by positivity) (show (0 : ℝ) ≤ q ^ n by positivity), 
              mul_nonneg (show (0 : ℝ) ≤ p ^ n by positivity) (show (0 : ℝ) ≤ r ^ n by positivity), 
                mul_nonneg (show (0 : ℝ) ≤ q ^ n by positivity) (show (0 : ℝ) ≤ r ^ n by positivity), 
                  mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3, 
                    sq_nonneg (p ^ n * q ^ n * r ^ n - 1)]
      linarith
    · -- Show the denominator is non-negative
      positivity
  linarith