import Mathlib

theorem algebra_299889 {a b c : ℝ} (h : a * b * c ≠ 0) (h1 : a + b + c = 2) (h2 : a^2 + b^2 + c^2 = 2) :
    (1 - a)^2 / (b * c) + (1 - b)^2 / (c * a) + (1 - c)^2 / (a * b) = 3 := by
  have h3 : a * b + b * c + c * a = 1 := by
    have h4 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h1, h2] at h4
    linarith
  
  have h5 : a ≠ 0 := by
    by_contra ha
    have : a * b * c = 0 := by
      rw [ha]
      ring
    contradiction
  
  have h6 : b ≠ 0 := by
    by_contra hb
    have : a * b * c = 0 := by
      rw [hb]
      ring
    contradiction
  
  have h7 : c ≠ 0 := by
    by_contra hc
    have : a * b * c = 0 := by
      rw [hc]
      ring
    contradiction

  have h8 : a^3 + b^3 + c^3 = 2 + 3 * (a * b * c) := by
    have h9 : a^3 + b^3 + c^3 = (a + b + c)^3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by ring
    rw [h1, h3] at h9
    linarith
  
  have eq1 : (1 - a)^2 / (b * c) + (1 - b)^2 / (c * a) + (1 - c)^2 / (a * b) =
    (a * (1 - a)^2 + b * (1 - b)^2 + c * (1 - c)^2) / (a * b * c) := by
    have hbc : b * c ≠ 0 := by
      apply mul_ne_zero
      · exact h6
      · exact h7
    have hca : c * a ≠ 0 := by
      apply mul_ne_zero
      · exact h7
      · exact h5
    have hab : a * b ≠ 0 := by
      apply mul_ne_zero
      · exact h5
      · exact h6
    field_simp [hbc, hca, hab]
    <;> ring
  
  rw [eq1]
  
  have eq2 : a * (1 - a)^2 + b * (1 - b)^2 + c * (1 - c)^2 = 3 * (a * b * c) := by
    have eq3 : a * (1 - a)^2 + b * (1 - b)^2 + c * (1 - c)^2 = (a + b + c) - 2 * (a^2 + b^2 + c^2) + (a^3 + b^3 + c^3) := by ring
    rw [eq3]
    rw [h1, h2, h8]
    all_goals linarith
  
  rw [eq2]
  field_simp [h]
  <;> nlinarith [mul_ne_zero (mul_ne_zero h5 h6) h7]