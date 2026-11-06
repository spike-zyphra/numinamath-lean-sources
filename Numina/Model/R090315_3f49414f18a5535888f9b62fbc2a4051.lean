import Mathlib

theorem algebra_321 {a b : ℝ} (ha : 0 < a) (h1 : a ^ 3 * b ^ 4 - a ^ 2 * b ^ 5 = 20) (h2 : a - b = 5) :
    a * b ^ 2 = 2 := by
  have h3 : a ^ 2 * b ^ 4 = 4 := by
    have h1' : a ^ 3 * b ^ 4 - a ^ 2 * b ^ 5 = a ^ 2 * b ^ 4 * (a - b) := by
      ring
    rw [h1'] at h1
    rw [h2] at h1
    linarith
  have h4 : (a * b ^ 2) ^ 2 = 4 := by
    nlinarith
  have h6 : a * b ^ 2 = 2 ∨ a * b ^ 2 = -2 := by
    have h7 : (a * b ^ 2) ^ 2 = 4 := h4
    have h8 : a * b ^ 2 = 2 ∨ a * b ^ 2 = -2 := by
      have h9 : (a * b ^ 2 - 2) * (a * b ^ 2 + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 => 
        left
        linarith
      | inr h11 => 
        right
        linarith
    tauto
  cases h6 with
  | inl h => 
    exact h
  | inr h6' => 
    -- $ab^2 = -2$ is contradicts $b^2 \geq 0$.
    have h6' : a * b ^ 2 = -2 := h6'
    nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a * b ^ 2), sq_pos_of_pos ha]