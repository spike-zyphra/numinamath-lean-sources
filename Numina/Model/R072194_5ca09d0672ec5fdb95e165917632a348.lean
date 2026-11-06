import Mathlib

theorem algebra_286321 {α β : ℝ} (h₀ : α + β = 17) (h₁ : α * β = 70) :
    |α - β| = 3 := by
  have h2 : (α - β) ^ 2 = 9 := by
    calc
      (α - β) ^ 2 = (α + β) ^ 2 - 4 * (α * β) := by ring
      _ = 17 ^ 2 - 4 * 70 := by rw [h₀, h₁]
      _ = 289 - 280 := by norm_num
      _ = 9 := by norm_num

  have h3 : (α - β) ^ 2 = 9 := h2

  have h4 : α - β = 3 ∨ α - β = -3 := by
    have h5 : (α - β) ^ 2 - 9 = 0 := by linarith
    have h6 : (α - β - 3) * (α - β + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h6) with
    | inl h7 =>
      left
      linarith
    | inr h8 =>
      right
      linarith

  cases h4 with
  | inl h7 =>
    rw [h7]
    norm_num
  | inr h8 =>
    rw [h8]
    norm_num