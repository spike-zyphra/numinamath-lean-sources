import Mathlib

theorem algebra_297166 {a b : ℝ} (h : (3 * a + 5 * b - 1) ^ 2 + abs (a + 3 * b + 1) = 0) :
    ∀ x, a * x - b > x / 3 + 6 ↔ x > 3 := by
  have h₁ : (3 * a + 5 * b - 1) ^ 2 = 0 := by 
    linarith [sq_nonneg (3 * a + 5 * b - 1), abs_nonneg (a + 3 * b + 1)]
  have h₂ : abs (a + 3 * b + 1) = 0 := by 
    linarith [sq_nonneg (3 * a + 5 * b - 1), abs_nonneg (a + 3 * b + 1)]
  have eq1 : 3 * a + 5 * b - 1 = 0 := by 
    rwa [sq_eq_zero_iff] at h₁
  have eq2 : a + 3 * b + 1 = 0 := by 
    rwa [abs_eq_zero] at h₂
  have ha : a = 2 := by 
    nlinarith
  have hb : b = -1 := by 
    nlinarith
  intro x
  constructor
  · -- Assume a * x - b > x / 3 + 6, prove x > 3
    intro h'
    rw [ha, hb] at h'
    linarith
  · -- Assume x > 3, prove a * x - b > x / 3 + 6
    intro h'
    rw [ha, hb]
    linarith