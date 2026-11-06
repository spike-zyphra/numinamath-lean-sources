import Mathlib

theorem algebra_251291 {a b c : ℝ} (ha : a ≠ 0) (h : ¬∃ x : ℝ, a * x ^ 2 + b * x + c = 0)
    (h1 : a + b + c < 0) : c < 0 := by 
  by_contra h2
  push_neg at h2
  have h4 : a > 0 ∨ a < 0 := by
    by_contra h
    push_neg at h
    have : a = 0 := by linarith
    contradiction
  cases h4 with
  | inl h3 =>
    exfalso 
    apply h
    have h5 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
      have h6 : b ^ 2 - 4 * a * c ≥ 0 := by 
        nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (c + a + b), sq_nonneg (c - a), sq_nonneg (a + b), sq_nonneg (c - b), sq_pos_of_ne_zero (show (a : ℝ) ≠ 0 by assumption)]
      use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
      field_simp [show (a : ℝ) ≠ 0 by assumption]
      ring_nf 
      rw [Real.sq_sqrt (by nlinarith)]
      <;> nlinarith 
    tauto
  | inr h4 =>
    exfalso 
    apply h
    have h5 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
      have h6 : b ^ 2 - 4 * a * c ≥ 0 := by 
        nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (c + a + b), sq_nonneg (c - a), sq_nonneg (a + b), sq_nonneg (c - b), sq_pos_of_ne_zero (show (a : ℝ) ≠ 0 by assumption)]
      use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
      field_simp [show (a : ℝ) ≠ 0 by assumption]
      ring_nf 
      rw [Real.sq_sqrt (by nlinarith)]
      <;> nlinarith 
    tauto