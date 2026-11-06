import Mathlib

theorem inequalities_3229 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h2a : a ≤ 2) (h2b : b ≤ 2) (h2c : c ≤ 2) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≤ 10 := by 
  have h1 : a > 0 := by linarith
  have h2 : b > 0 := by linarith
  have h3 : c > 0 := by linarith
  have h5 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 10 ≤ 0 := by
    have h6 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 10 =
        ((a + b + c) * (b * c + a * c + a * b) - 10 * a * b * c) / (a * b * c) := by 
      field_simp
      ring
    rw [h6]
    have h7 : a * b * c > 0 := by
      positivity
    have h8 : ((a + b + c) * (b * c + a * c + a * b) - 10 * a * b * c) ≤ 0 := by 
      nlinarith [mul_nonneg (sub_nonneg.mpr h2a) (sub_nonneg.mpr h2b), 
          mul_nonneg (sub_nonneg.mpr h2a) (sub_nonneg.mpr h2c), 
          mul_nonneg (sub_nonneg.mpr h2b) (sub_nonneg.mpr h2c), 
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb), 
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc), 
          mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc), 
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h2a), 
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h2b), 
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h2c), 
          mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h2a), 
          mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h2b), 
          mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h2c), 
          mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2a), 
          mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2b), 
          mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2c)
          ]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    all_goals
      positivity
  linarith