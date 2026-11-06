import Mathlib

theorem algebra_13629 {x y : ℝ} (h₀ : x + y = 25) (h₁ : x * y = 126) :
    |x - y| = 11 := by 
  have h2 : (x - y) ^ 2 = 121 := by
    calc
      (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by ring
      _ = 25 ^ 2 - 4 * 126 := by rw [h₀, h₁]
      _ = 625 - 4 * 126 := by norm_num
      _ = 625 - 504 := by norm_num
      _ = 121 := by norm_num

  have h3 : x - y = 11 ∨ x - y = -11 := by
    have h4 : (x - y) ^ 2 = 121 := h2
    have h5 : (x - y) ^ 2 - 121 = 0 := by linarith
    have h6 : (x - y - 11) * (x - y + 11) = 0 := by
      linarith [h5]
    cases (mul_eq_zero.1 h6) with
    | inl h7 =>
      left
      linarith
    | inr h8 =>
      right
      linarith

  cases h3 with
  | inl h4 =>
    rw [h4]
    norm_num
  | inr h5 =>
    rw [h5]
    norm_num