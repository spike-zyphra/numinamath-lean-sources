import Mathlib

theorem algebra_287696 {a : ℝ} (ha : a = (1 + Real.sqrt 2009) / 2) : (a^3 - 503 * a - 500)^10 = 1024 := by
  have h1 : 2 * a - 1 = Real.sqrt 2009 := by 
    rw [ha]
    ring
  have h2 : (2 * a - 1) ^ 2 = 2009 := by 
    rw [h1]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h3 : 4 * a^2 - 4 * a - 2008 = 0 := by
    nlinarith
  have h4 : a^2 = a + 502 := by
    nlinarith
  have h5 : a^3 = 503 * a + 502 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 502) := by rw [h4]
      _ = a^2 + 502 * a := by ring
      _ = (a + 502) + 502 * a := by rw [h4]
      _ = 503 * a + 502 := by ring
  have h6 : a^3 - 503 * a - 500 = 2 := by
    rw [h5]
    linarith
  rw [h6]
  norm_num