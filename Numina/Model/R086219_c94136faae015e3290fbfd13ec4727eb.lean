import Mathlib

theorem algebra_309018 {a b : ℝ} (hab : a^2 * (b^2 + 1) + b * (b + 2 * a) = 40 ∧ a * (b + 1) + b = 8) :
    1 / a^2 + 1 / b^2 = 8 := by
  have eq1 : a^2 * (b^2 + 1) + b * (b + 2 * a) = 40 := hab.1
  have eq2 : a * (b + 1) + b = 8 := hab.2
  have h1 : a * b = 8 - a - b := by
    nlinarith 
  have h2 : a ^ 2 * (b ^ 2 + 1) + b * (b + 2 * a) = (a * b) ^ 2 + (a + b) ^ 2 := by 
    ring_nf
  rw [h2] at eq1
  rw [h1] at eq1 
  have h3 : (8 - (a + b)) ^ 2 + (a + b) ^ 2 = 40 := by 
    nlinarith 
  have h4 : (a + b) ^ 2 - 8 * (a + b) + 12 = 0 := by 
    nlinarith 
  have h5 : (a + b - 2) * (a + b - 6) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h5) with h6 h7 
  · -- Case $a + b = 2$
    have h8 : a + b = 2 := by linarith 
    have h9 : a * b = 6 := by 
      nlinarith 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * (a * b))] 
  · -- Case $a + b = 6$
    have h8 : a + b = 6 := by linarith 
    have h9 : a * b = 2 := by 
      nlinarith 
    have ha : a ≠ 0 := by
      by_contra h
      rw [h] at h9 
      have : 0 * b = 2 := by linarith 
      nlinarith 
    have hb : b ≠ 0 := by
      by_contra h
      rw [h] at h9 
      have : a * 0 = 2 := by linarith 
      nlinarith 
    field_simp [ha, hb]
    nlinarith [h8, h9]