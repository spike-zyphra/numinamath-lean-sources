import Mathlib

theorem algebra_234494 {a b c : ℝ} (ha : a ≠ 0) (h1 : a * ((a - b - c) / (2 * a))^2 + b * ((a - b - c) / (2 * a)) + c = 0)
    (h2 : a * ((c - a - b) / (2 * a))^2 + b * ((c - a - b) / (2 * a)) + c = 0) :
    (a * (-1)^2 + b * (-1) + c) * (a * 1^2 + b * 1 + c) = 0 := by
  have eq3 : a * ((a - b - c) / (2 * a))^2 + b * ((a - b - c) / (2 * a)) + c = 0 := h1
  have eq4 : a * ((c - a - b) / (2 * a))^2 + b * ((c - a - b) / (2 * a)) + c = 0 := h2
  have eq5 : (a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * a * c = 0 := by
    have h3 : a ≠ 0 := ha
    field_simp [show a ≠ 0 by exact h3] at eq3 ⊢
    ring_nf at eq3 ⊢
    <;> nlinarith [sq_nonneg (a - b - c), sq_nonneg (c - a - b), sq_pos_of_ne_zero (show a ≠ 0 by exact h3)]
  
  have eq6 : (c - a - b) ^ 2 + 2 * b * (c - a - b) + 4 * a * c = 0 := by
    have h3 : a ≠ 0 := ha
    field_simp [show a ≠ 0 by exact h3] at eq4 ⊢
    ring_nf at eq4 ⊢
    <;> nlinarith [sq_nonneg (c - a - b), sq_nonneg (a - b - c), sq_pos_of_ne_zero (show a ≠ 0 by exact h3)]
  
  have h5 : a^2 + 2 * a * c + c^2 - b^2 = 0 := by
    nlinarith [eq5, eq6]
  
  have factored : (a + c - b) * (a + c + b) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp factored) with h6 h7
  · -- Case h6 : a + c - b = 0
    have eq5 : a * (-1)^2 + b * (-1) + c = 0 := by
      have h3 : a - b + c = 0 := by linarith
      linarith
    have eq6 : (a * (-1)^2 + b * (-1) + c) * (a * 1^2 + b * 1 + c) = 0 := by
      rw [eq5]
      norm_num
    exact eq6
  
  · -- Case h7 : a + c + b = 0
    have eq7 : a * 1^2 + b * 1 + c = 0 := by
      have h3 : a + b + c = 0 := by linarith
      linarith
    have eq9 : (a * (-1)^2 + b * (-1) + c) * (a * 1^2 + b * 1 + c) = 0 := by
      rw [eq7]
      norm_num
    exact eq9