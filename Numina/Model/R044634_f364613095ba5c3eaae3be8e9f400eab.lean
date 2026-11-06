import Mathlib

theorem algebra_254380 {x : ℕ} (hx : 3^(2*x) + 9 = 10 * 3^x) :
    x^2 + 1 = 1 ∨ x^2 + 1 = 5 := by 
  have h1 : (3 : ℕ) ^ (2 * x) = ((3 ^ x) ^ 2) := by 
    ring_nf
  rw [h1] at hx
  have h5 : ((3 ^ x) : ℕ) ≤ 9 := by
    by_contra h5
    push_neg at h5
    have h5 : ((3 ^ x) : ℕ) ≥ 10 := by linarith
    nlinarith [sq_nonneg (( (3 ^ x) : ℕ ) - 1 : ℤ), sq_nonneg (( (3 ^ x) : ℕ ) - 9 : ℤ), sq_nonneg (( (3 ^ x) : ℕ ) : ℤ), sq_nonneg ((10 : ℤ) : ℤ)]
  have h2 : ((3 : ℕ) ^ x) = 1 ∨ ((3 : ℕ) ^ x) = 9 := by 
    interval_cases h3 : ((3 : ℕ) ^ x) <;> omega
  cases h2 with
  | inl h3 =>
    have h4 : x = 0 := by
      have h5 : (3 : ℕ) ^ x = 1 := h3
      have h6 : x = 0 := by
        have h7 : (3 : ℕ) ^ x = 1 := h5
        exact Nat.pow_right_injective (by norm_num) h7
      exact h6
    left
    rw [h4]
    all_goals norm_num
  | inr h3 =>
    have h4 : x = 2 := by
      have h5 : (3 : ℕ) ^ x = 9 := h3
      have h6 : x = 2 := by
        have h7 : (3 : ℕ) ^ x = 9 := h5
        exact Nat.pow_right_injective (by norm_num) h7
      exact h6
    right
    rw [h4]
    all_goals norm_num