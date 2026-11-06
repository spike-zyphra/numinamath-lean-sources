import Mathlib

theorem algebra_212742 {a b c : ℝ} (h₀ : a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b + 3 * a * b * c = 30) (h₁ : a^2 + b^2 + c^2 = 13) : a + b + c = 5 := by
  have eq1 : a ^ 2 * b + a ^ 2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b + 3 * a * b * c = (a + b + c) * (a * b + a * c + b * c) := by 
    ring 
  rw [eq1] at h₀
  have eq2 : a ^ 2 + b^2 + c^2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
    ring
  rw [eq2] at h₁
  have eq3 : (a + b + c)^3 - 13 * (a + b + c) - 60 = 0 := by
    have h2 : a + b + c ≠ 0 := by
      by_contra h
      have h00 : a + b + c = 0 := by
        linarith
      rw [h00] at h₀
      nlinarith
    have eq4 : a * b + a * c + b * c = 30 / (a + b + c) := by
      field_simp [h2]
      nlinarith 
    rw [eq4] at h₁ 
    field_simp [h2] at h₁ 
    nlinarith [sq_pos_of_pos (show 0 < (1 : ℝ) by norm_num)]
  have eq4 : (a + b + c - 5) * ((a + b + c)^2 + 5 * (a + b + c) + 12) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq4) with h h'
  · -- Case a + b + c - 5 = 0
    linarith 
  · -- Case (a + b + c)^2 + 5(a + b + c) + 12 = 0 
    nlinarith [sq_nonneg ((a + b + c) + 5 / 2)]