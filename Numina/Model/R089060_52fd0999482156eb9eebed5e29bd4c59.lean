import Mathlib

theorem algebra_141 {a b c : ℝ} (_ : a ≠ 0) (h : 1 / 4 * (b - c) ^ 2 = (a - b) * (c - a)) :
    (b + c) / a = 2 := by

  have h1 : (b - c) ^ 2 = 4 * (a - b) * (c - a) := by 
    linarith
  
  have h2 : (b + c) ^ 2 - 4 * a * (b + c) + 4 * a ^ 2 = 0 := by
    nlinarith [h1]

  have h3 : (b + c - 2 * a) ^ 2 = 0 := by
    nlinarith [h2]

  have h4 : b + c - 2 * a = 0 := by
    rw [sq_eq_zero_iff] at h3
    exact h3

  have h5 : b + c = 2 * a := by
    linarith

  have h6 : (b + c) / a = 2 := by
    rw [h5]
    field_simp
    <;> nlinarith
  exact h6