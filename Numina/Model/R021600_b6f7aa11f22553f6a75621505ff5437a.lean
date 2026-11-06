import Mathlib

theorem algebra_254850 (a b c : ℝ) (ha : a ≠ 0) (hroots : ¬∃ x : ℝ, a * x ^ 2 + b * x + c = 0)
    (hsum : a + b + c > 0) : c > 0 := by
  by_contra h
  push_neg at h
  have h1 : ∀ x : ℝ, a * x ^ 2 + b * x + c ≠ 0 := by
    intro x
    by_contra h2
    have : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := ⟨x, by linarith⟩
    contradiction
  have h6 : b ^ 2 - 4 * a * c < 0 := by 
    by_contra h7
    push_neg at h7
    have h8 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by 
      have h8 : (b : ℝ) ^ 2 - 4 * a * c ≥ 0 := by linarith
      use (-b + Real.sqrt ((b) ^ 2 - 4 * a * c)) / (2 * a)
      field_simp 
      nlinarith [Real.sqrt_nonneg ((b : ℝ) ^ 2 - 4 * a * c), Real.sq_sqrt (show (b ^ 2 - 4 * a * c) ≥ 0 by linarith)]
    have h10 := h1 (h8.choose)
    contradiction 
  by_cases ha' : a > 0
  · -- Assume a > 0 
    have h7 : c ≥ 0 := by
      nlinarith [sq_nonneg (b + 2 * a * c), sq_nonneg (b ^ 2 - 4 * a * c), sq_nonneg ((b) + 2 * a), sq_nonneg ((b) - 2 * a), sq_nonneg (c), hsum, mul_pos ha' (show 0 < (1 : ℝ) by norm_num), mul_self_nonneg (a), mul_self_nonneg (b)]
    nlinarith 
  · -- Assume a ≤ 0 
    push_neg at ha'
    have ha1 : a ≤ 0 := by linarith 
    have h7 : c ≥ 0 := by 
      nlinarith [sq_nonneg (b + 2 * a * c), sq_nonneg (b ^ 2 - 4 * a * c), sq_nonneg ((b) + 2 * a), sq_nonneg ((b) - 2 * a), sq_nonneg (c), hsum, mul_pos (show 0 < (1 : ℝ) by norm_num) (show 0 < (1 : ℝ) by norm_num), mul_self_nonneg (a), mul_self_nonneg (b)]
    nlinarith