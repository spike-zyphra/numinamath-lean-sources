import Mathlib

theorem algebra_250478 {a b c d : ℝ} (h₀ : b ≠ 1) (h₁ : c ≠ 1)
    (h₂ : a * c - a - c = b ^ 2 - 2 * b) (h₃ : b * d - b - d = c ^ 2 - 2 * c) :
    a * d + b + c = b * c + a + d := by
  have h4 : (a - 1) * (c - 1) = (b - 1) ^ 2 := by
    nlinarith
  have h5 : (b - 1) * (d - 1) = (c - 1) ^ 2 := by
    nlinarith 
  have h6 : c - 1 ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h7 : b - 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  have eq1 : a = 1 + (b - 1) ^ 2 / (c - 1) := by
    have h6 : c - 1 ≠ 0 := by
      intro h
      apply h₁
      linarith
    field_simp [h6]
    <;> nlinarith [h4]
  have eq2 : d = 1 + (c - 1) ^ 2 / (b - 1) := by
    have h7 : b - 1 ≠ 0 := by
      intro h
      apply h₀
      linarith
    field_simp [h7]
    <;> nlinarith [h5]
  rw [eq1, eq2]
  have h6 : c - 1 ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h7 : b - 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  field_simp [(show c - 1 ≠ 0 by exact h6), 
    (show b - 1 ≠ 0 by exact h7)]
  <;> nlinarith [sq_pos_of_ne_zero (show c - 1 ≠ 0 by exact h6), sq_pos_of_ne_zero (show b - 1 ≠ 0 by exact h7)]