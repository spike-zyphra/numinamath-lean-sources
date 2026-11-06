import Mathlib

theorem algebra_187074 {x y : ℝ} (h1 : x ^ 2 * y + x * y ^ 2 = 6) (h2 : x * y + x + y = 5) :
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) := by
  have h3 : x * y * (x + y) = 6 := by
    have h : x ^ 2 * y + x * y ^ 2 = x * y * (x + y) := by
      ring
    rw [h] at h1
    linarith
  have h4 : x * y + x + y = 5 := h2
  have h5 : (x + y) ^ 2 - 5 * (x + y) + 6 = 0 := by
    have h6 : x * y = 5 - (x + y) := by
      nlinarith [h4]
    rw [h6] at h3
    nlinarith [h3]
  have h6 : (x + y - 3) * (x + y - 2) = 0 := by
    nlinarith [h5]
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- case x + y = 3
    have h7' : x + y = 3 := by linarith
    have h8' : x * y = 2 := by
      nlinarith [h4, h7']
    have h10 : (x - 1) * (x - 2) = 0 := by
      have h11 : y = 3 - x := by linarith
      rw [h11] at h8'
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- case x = 1
      have hx1 : x = 1 := by linarith
      have hy1 : y = 2 := by linarith [h7', hx1]
      left
      exact ⟨hx1, hy1⟩
    · -- case x = 2
      have hx2 : x = 2 := by linarith
      have hy1 : y = 1 := by linarith [h7', hx2]
      right
      exact ⟨hx2, hy1⟩
  · -- case x + y = 2
    have h8' : x + y = 2 := by linarith
    have h9' : x * y = 3 := by
      nlinarith [h4, h8']
    nlinarith [sq_nonneg (x - y), h8', h9']