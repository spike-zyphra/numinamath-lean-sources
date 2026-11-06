import Mathlib

theorem algebra_214033 {x y : ℝ} (hx : x * y ≥ 0) (h1 : x + y + Real.sqrt (x * y) = 28) (h2 : x ^ 2 + y ^ 2 + x * y = 336) :
    (x = 4 ∧ y = 16) ∨ (x = 16 ∧ y = 4) := by
  have h3 : Real.sqrt (x * y) ≥ 0 := by positivity
  have h4 : (Real.sqrt (x * y)) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    linarith
  have h5 : (x + y) ^ 2 + 2 * (x + y) * Real.sqrt (x * y) + (Real.sqrt (x * y) ^ 2) = 784 := by
    have h6 : (x + y + Real.sqrt (x * y)) ^ 2 = 28 ^ 2 := by
      rw [h1]
    nlinarith
  rw [h4] at h5
  have h3 : (x + y) ^ 2 - (x * y) = 336 := by
    nlinarith [h2]
  have h9 : x * y + (x + y) * Real.sqrt (x * y) = 224 := by
    nlinarith [h5, h3]
  have h10 : Real.sqrt (x * y) = 8 := by
    nlinarith [h1, h9]
  have h11 : x * y = 64 := by
    have h12 : (Real.sqrt (x * y)) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      nlinarith
    rw [h10] at h12
    nlinarith
  have h13 : x + y = 20 := by
    nlinarith [h1, h10]
  have h14 : (x - 4) * (x - 16) = 0 := by
    have h15 : x + y = 20 := by
      exact h13
    have h16 : x * y = 64 := by
      nlinarith [h11]
    have h17 : y = 20 - x := by
      linarith
    rw [h17] at h16
    nlinarith
  cases' (mul_eq_zero.mp h14) with h15 h16
  · -- x - 4 = 0
    have hx1 : x = 4 := by linarith
    have hy1 : y = 16 := by linarith
    left
    constructor
    · exact hx1
    · exact hy1
  · -- x - 16 = 0
    have hx2 : x = 16 := by linarith
    have hy2 : y = 4 := by linarith
    right
    constructor
    · exact hx2
    · exact hy2