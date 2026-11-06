import Mathlib

theorem algebra_161641 {x y : ℝ} (h1 : 2 * x + y + 2 * x * y = 11) (h2 : 2 * x ^ 2 * y + x * y ^ 2 = 15) :
    (x = 1 / 2 ∧ y = 5) ∨ (x = 1 ∧ y = 3) ∨ (x = 3 / 2 ∧ y = 2) ∨ (x = 5 / 2 ∧ y = 1) := by
  have eq1 : 2 * x ^ 2 * y + x * y ^ 2 = x * y * (2 * x + y) := by
    ring
  rw [eq1] at h2
  have h4 : (x * y - 3) * (x * y - 5 / 2) = 0 := by
    nlinarith [sq_nonneg (x * y), sq_nonneg (2 * x + y), sq_nonneg (2 * x + y - 5), sq_nonneg (2 * x + y - 6)]
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- case where x * y = 3
    have h7 : x * y = 3 := by linarith
    have h8 : 2 * x + y = 5 := by
      nlinarith [h7, h1]
    have h9 : (x - 1) * (x - 3 / 2) = 0 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (x - 1), sq_nonneg (x - 3 / 2)]
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- x = 1
      have hx1 : x = 1 := by linarith
      have hy1 : y = 3 := by
        nlinarith [h1, hx1, h7]
      simp [hx1, hy1]
      <;> tauto
    · -- x = 3/2
      have hx2 : x = 3 / 2 := by linarith
      have hy2 : y = 2 := by
        nlinarith [h1, hx2, h7]
      simp [hx2, hy2]
      <;> tauto
  · -- case where x * y = 5/2
    have h7 : x * y = 5 / 2 := by linarith
    have h8 : 2 * x + y = 6 := by
      nlinarith [h7, h1]
    have h9 : (x - 5 / 2) * (x - 1 / 2) = 0 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (x - 5 / 2), sq_nonneg (x - 1 / 2)]
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- x = 5/2
      have hx3 : x = 5 / 2 := by linarith
      have hy3 : y = 1 := by
        nlinarith [h1, hx3, h7]
      simp [hx3, hy3]
      <;> tauto
    · -- x = 1/2
      have hx4 : x = 1 / 2 := by linarith
      have hy4 : y = 5 := by
        nlinarith [h1, hx4, h7]
      simp [hx4, hy4]
      <;> tauto