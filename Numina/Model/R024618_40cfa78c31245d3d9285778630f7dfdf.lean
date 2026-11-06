import Mathlib

theorem algebra_949 {a b c x : ℝ} (ha : a + x^2 = 2011) (hb : b + x^2 = 2012) (hc : c + x^2 = 2013) (habc : a * b * c = 24) : a / (b * c) + c / (a * b) + b / (a * c) - 1 / a - 1 / b - 1 / c = 1 / 8 := by
  have h1 : b = a + 1 := by
    nlinarith
  have h2 : c = a + 2 := by
    nlinarith
  have eq1 : a * b * c = 24 := habc
  rw [show b = a + 1 by linarith [h1]] at eq1
  rw [show c = a + 2 by linarith [h2]] at eq1
  have h3 : a * (a + 1) * (a + 2) = 24 := by
    linarith [eq1]
  have h4 : a^3 + 3 * a^2 + 2 * a - 24 = 0 := by
    nlinarith
  have h5 : (a - 2) * (a^2 + 5 * a + 12) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- The case a - 2 = 0, so a = 2
    have ha1 : a = 2 := by
      linarith
    have hb1 : b = 3 := by 
      nlinarith [ha1, h1]
    have hc1 : c = 4 := by 
      nlinarith [ha1, h2]
    have ha_nz : a ≠ 0 := by 
      linarith [ha1]
    have hb_nz : b ≠ 0 := by 
      linarith [hb1]
    have hc_nz : c ≠ 0 := by 
      linarith [hc1]
    have hbc_nz : b * c ≠ 0 := by
      apply mul_ne_zero 
      linarith [hb1]
      linarith [hc1]
    have hab_nz : a * b ≠ 0 := by 
      apply mul_ne_zero 
      linarith [ha1]
      linarith [hb1]
    have hac_nz : a * c ≠ 0 := by 
      apply mul_ne_zero 
      linarith [ha1]
      linarith [hc1]
    rw [ha1, hb1, hc1]
    norm_num
    all_goals field_simp
  · -- Show that the quadratic is impossible
    nlinarith [sq_nonneg (a + 5 / 2)]