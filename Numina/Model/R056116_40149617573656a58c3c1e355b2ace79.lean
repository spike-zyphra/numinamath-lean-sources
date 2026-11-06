import Mathlib

theorem algebra_187057 {x y : ℝ} (h1 : y^2 - x * y = -12) (h2 : x^2 - x * y = 28) :
    (x, y) = (-7, -3) ∨ (x, y) = (7, 3) := by
  have h3 : (x - y) ^ 2 = 16 := by
    nlinarith
  have h4 : x - y = 4 ∨ x - y = -4 := by
    have h5 : (x - y) ^ 2 - 16 = 0 := by linarith
    have h6 : (x - y - 4) * (x - y + 4) = 0 := by
      nlinarith [h5]
    cases (mul_eq_zero.1 h6) with
    | inl h7 =>
      left
      linarith
    | inr h8 =>
      right
      linarith
  cases h4 with
  | inl h4_4 =>
    have h5 : y = 3 := by
      have h5 : x = y + 4 := by linarith
      rw [h5] at h2
      nlinarith
    have hx : x = 7 := by
      linarith [h5, h4_4]
    have h3 : (x, y) = (7, 3) := by
      simp [hx, h5]
    right
    exact h3
  | inr h4_neg4 =>
    have h5 : y = -3 := by
      have h5 : x = y - 4 := by linarith
      rw [h5] at h2
      nlinarith
    have hx : x = -7 := by
      linarith [h5, h4_neg4]
    have h3 : (x, y) = (-7, -3) := by
      simp [hx, h5]
    left
    exact h3