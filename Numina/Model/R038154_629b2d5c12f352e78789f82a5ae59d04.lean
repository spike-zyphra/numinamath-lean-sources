import Mathlib

theorem inequalities_603022 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    ((1 / a^3 - a^2) * (1 / b^3 - b^2)) ≥ (31 / 4)^2 := by
  have h1 : b = 1 - a := by linarith
  rw [h1]
  have h2 : a * (1 - a) > 0 := by
    apply mul_pos
    linarith
    linarith
  have h3 : a > 0 := by linarith
  have h4 : (1 - a) > 0 := by nlinarith
  have h5 : (1 / a ^ 3 - a ^ 2) * (1 / (1 - a) ^ 3 - (1 - a) ^ 2) ≥ (31 / 4) ^ 2 := by
    have h6 : 0 < a ^ 3 * (1 - a) ^ 3 := by
      positivity
    have h7 : (1 / a ^ 3 - a ^ 2) * (1 / (1 - a) ^ 3 - (1 - a) ^ 2) =
        ((1 - a^5) * (1 - (1 - a) ^5)) / (a^3 * (1 - a) ^3) := by
        field_simp
        ring_nf
    rw [h7] at *
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a^2 - (1 / 4)), sq_nonneg (a * (1 - a) - 1 / 4),
              sq_nonneg (a ^ 2 - (1 - a) ^2), sq_nonneg (a * a - (1 - a) * (1 - a)), 
              mul_pos h3 (show 0 < (1 - a) by nlinarith),
              sq_nonneg (a ^ 2 - (1 / 4)), sq_nonneg ((1 - a) ^2 - (1 / 4)), 
              sq_nonneg (a - (1 - a)), sq_nonneg (a * (1 - a) - 1 / 4), 
              sq_nonneg ((a ^ 2 - (1 - a) ^ 2)), 
              sq_nonneg (a * (a - 1 / 2) ), sq_nonneg ((1 - a) * ( (1 - a) - 1 / 2) ), 
              sq_nonneg (a * a * ( a - 1 / 2 )), sq_nonneg ( (1 - a) * (1 - a) * ( (1 - a) - 1 / 2 ) ), 
              sq_nonneg (a * (1 - a) * (a - 1 / 2) ), sq_nonneg (a * (1 - a) * (a - 1 / 2 ) ), 
              mul_pos h3 (show (0: ℝ) < 1 - a by linarith), 
              sq_nonneg (a - 1 / 2), sq_nonneg (a * (a - 1 / 2) ), sq_nonneg (a * (1 - a) ), 
              h, mul_pos h3 (show (0: ℝ) < 1 - a by linarith) ]
  linarith