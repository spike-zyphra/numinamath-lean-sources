import Mathlib


theorem algebra_610726 (a b c : ℝ) (h1: a+b+c = 100) (h2: a*b + b*c  + c*a = 20) (h3: (a+b)*(a+c) = 24): (b*c = -176)∨(b*c = 224) := by
  have h4 : a^2 = 4 := by
    have h4 : (a + b) * (a + c) = a ^ 2 + a * b + a * c + b * c := by ring
    rw [h4] at h3
    have h5 : a * b + b * c + c * a = 20 := by
      linarith
    nlinarith
  have h5 : a = 2 ∨ a = -2 := by
    have h6 : a^2 - 4 = 0 := by linarith
    have h7 : (a - 2) * (a + 2) = 0 := by
      linarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · left
      linarith
    · right
      linarith
  cases h5 with
  | inl ha2 =>
    have h6 : b + c = 98 := by
      linarith [h1, ha2]
    have h7 : b * c = -176 := by
      have eq1 : a * b + b * c + c * a = 20 := by
        linarith [h2]
      rw [ha2] at eq1
      have eq2 : 2 * (b + c) + b * c = 20 := by
        linarith
      rw [show b + c = (98 : ℝ) by linarith] at eq2
      linarith
    left
    linarith [h7]
  | inr ha2 =>
    have h8 : b + c = 102 := by
      linarith [h1, ha2]
    have h9 : b * c = 224 := by
      have eq1 : a * b + b * c + c * a = 20 := by
        linarith [h2]
      rw [ha2] at eq1
      have eq2 : -2 * (b + c) + b * c = 20 := by
        linarith
      rw [show b + c = (102 : ℝ) by linarith] at eq2
      linarith
    right
    linarith [h9]