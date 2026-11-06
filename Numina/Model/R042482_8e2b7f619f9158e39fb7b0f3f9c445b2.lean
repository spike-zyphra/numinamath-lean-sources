import Mathlib

theorem algebra_598498 (a b c d : ℝ) (h₀ : a + b + c + d = 3) (h₁ : a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 6 * d ^ 2 = 5) :
    1 ≤ a ∧ a ≤ 2 := by
  have h3 : b + c + d = 3 - a := by 
    linarith
  have h4 : 2 * b ^ 2 + 3 * c ^ 2 + 6 * d ^ 2 = 5 - a ^ 2 := by
    nlinarith
  have h5 : 2 * b ^ 2 + 3 * c ^ 2 + 6 * d ^ 2 ≥ (b + c + d) ^ 2 := by 
    nlinarith [sq_nonneg (b - (c + d)), sq_nonneg (c - 2 * d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  have h5' : 5 - a ^ 2 ≥ (3 - a) ^ 2 := by
    have eq5 : 2 * b ^ 2 + 3 * c ^ 2 + 6 * d ^ 2 = 5 - a ^ 2 := h4
    have eq5' : (b + c + d) ^ 2 = (3 - a) ^ 2 := by
      rw [h3]
    nlinarith [h5, eq5, eq5']
  have h8 : a ≥ 1 := by
    nlinarith
  have h9 : a ≤ 2 := by
    nlinarith
  constructor
  · linarith
  · linarith