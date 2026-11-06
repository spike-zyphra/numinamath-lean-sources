import Mathlib

theorem algebra_186658 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a < b)
    (h1 : Real.sqrt (a * b) = 60 / 100 * (a + b) / 2) :
    a / b = 1 / 9 := by

  have h1' : 0 < a * b := by
    nlinarith
  have h2 : (Real.sqrt (a * b)) ^ 2 = (60 / 100 * (a + b) / 2) ^ 2 := by
    rw [h1]
  have h3 : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by
    nlinarith
  )
  rw [h3] at h2
  have h4 : a * b = (60 / 100 * (a + b) / 2) ^ 2 := by
    linarith
  have h5 : a * b = 9 / 100 * (a + b) ^ 2 := by
    nlinarith [h4]
  have h6 : 100 * (a * b) = 9 * (a + b) ^ 2 := by
    nlinarith [h5]
  have h7 : 100 * (a * b) = 9 * (a^2 + 2 * (a * b) + b^2) := by
    nlinarith [h6]
  have h8 : 9 * a^2 - 82 * (a * b) + 9 * b^2 = 0 := by
    nlinarith [h7]

  have h9 : (9 * a - b) * (a - 9 * b) = 0 := by
    nlinarith [h8]
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- Case 1: When 9*a - b =0
    have h12 : b = 9 * a := by
      nlinarith
    have h13 : a / b = 1 / 9 := by
      rw [h12]
      have h14 : a ≠ 0 := by linarith
      field_simp [h14]
      <;> nlinarith
    exact h13
  · -- Case 2: When a - 9*b =0
    have h15 : a = 9 * b := by
      nlinarith
    nlinarith [show 0 < b from hb, h15]