import Mathlib

theorem algebra_308648 {a b c : ℝ} (h₀ : a - b + c = 7) (h₁ : a * b + b * c + b + c^2 + 16 = 0) :
    b / a = -4 / 3 := by
  have hc : c = 7 - a + b := by
    linarith
  rw [hc] at h₁
  have h2 : a ^ 2 - 2 * a * b + 2 * b ^ 2 - 14 * a + 22 * b + 65 = 0 := by
    nlinarith
  have h3 : (b + 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - (b + 4)), sq_nonneg (b + 4)]
  have hb : b = -4 := by
    nlinarith
  have ha : a = 3 := by
    rw [hb] at h2
    have h4 : (a - 3) ^ 2 = 0 := by
      nlinarith
    have ha2 : a - 3 = 0 := by
      apply pow_eq_zero 
      exact h4
    linarith
  have h_a_ne_zero : a ≠ 0 := by
    linarith [ha]
  have hfrac : b / a = -4 / 3 := by
    rw [hb, ha]
  exact hfrac