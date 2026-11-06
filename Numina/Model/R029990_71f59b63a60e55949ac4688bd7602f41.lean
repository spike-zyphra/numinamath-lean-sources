import Mathlib

theorem algebra_312608 {a b c : ℝ} (ha : a + b + c = 3) (hb : a^2 + b^2 + c^2 = 4) :
    (a^2 + b^2) / (2 - c) + (b^2 + c^2) / (2 - a) + (c^2 + a^2) / (2 - b) = 9 := by

  have h1 : 2 - c ≠ 0 := by
    by_contra h
    have h2 : c = 2 := by linarith
    have h3 : a + b = 1 := by linarith [ha, h2]
    have h4 : a^2 + b^2 = 0 := by nlinarith [hb, h2, h3]
    have h5 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h4]
    have h6 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h4]
    nlinarith

  have h2 : 2 - a ≠ 0 := by
    by_contra h
    have h2 : a = 2 := by linarith
    have h3 : b + c = 1 := by linarith [ha, h2]
    have h4 : b^2 + c^2 = 0 := by nlinarith [hb, h2, h3]
    have h5 : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, h4]
    have h6 : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, h4]
    nlinarith

  have h3 : 2 - b ≠ 0 := by 
    by_contra h 
    have h2 : b = 2 := by linarith
    have h3 : a + c = 1 := by linarith [ha, h2]
    have h4 : a^2 + c^2 = 0 := by nlinarith [hb, h2, h3]
    have h5 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg c, h4]
    have h6 : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg c, h4]
    nlinarith

  have h4 : a^2 + b^2 = 4 - c^2 := by 
    nlinarith

  have h5 : b^2 + c^2 = 4 - a^2 := by 
    nlinarith

  have h6 : c^2 + a^2 = 4 - b^2 := by 
    nlinarith

  have eq1 : (a^2 + b^2) / (2 - c) = c + 2 := by 
    rw [h4]
    field_simp [(show 2 - c ≠ 0 by assumption)]
    <;> nlinarith

  have eq2 : (b^2 + c^2) / (2 - a) = a + 2 := by 
    rw [h5]
    field_simp [(show 2 - a ≠ 0 by assumption)]
    <;> nlinarith

  have eq3 : (c^2 + a^2) / (2 - b) = b + 2 := by 
    rw [h6]
    field_simp [(show 2 - b ≠ 0 by assumption)]
    <;> nlinarith

  rw [eq1, eq2, eq3]
  nlinarith [ha]