import Mathlib

theorem algebra_316527 {a b : ℝ} (ha : a^2 + 2 * a - 1 = 0) (hb : b^4 - 2 * b^2 - 1 = 0)
    (h : 1 - a * b^2 ≠ 0) :
    ((a * b^2 + b^2 + 1) / a)^1990 = 1 := by
  have ha1 : a ≠ 0 := by
    by_contra h1
    have h1 : a = 0 := by linarith
    rw [h1] at ha
    nlinarith

  have h2 : (b^2 + a) * (b^2 - a - 2) = 0 := by
    nlinarith [sq_nonneg (b^2), sq_nonneg (a - 1), sq_nonneg (a - b^2), sq_nonneg (a + 1)]

  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case b^2 + a = 0
    have h5 : b^2 = -a := by linarith
    have eq1 : a * b^2 + b^2 + 1 = a := by
      rw [show b^2 = -a by linarith]
      nlinarith [ha]
    have eq2 : (a * b^2 + b^2 + 1) / a = 1 := by
      rw [eq1]
      field_simp [ha1]
    rw [eq2]
    all_goals norm_num

  · -- Case b^2 - a - 2 = 0
    have h6 : b^2 = a + 2 := by linarith
    have h7 : 1 - a * b^2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b^2), h6, ha]
    contradiction