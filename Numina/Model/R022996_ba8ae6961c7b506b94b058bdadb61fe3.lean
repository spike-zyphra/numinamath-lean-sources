import Mathlib

theorem algebra_276736 (a b c : ℝ) (h : ¬(a = b ∧ b = c)) :
    ¬∃ x : ℝ, (a^2 + b^2 + c^2)*x^2 + 2*(a + b + c)*x + 3 = 0 := by
  rintro ⟨x, hx⟩
  have h1 : (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 > 0 := by
    by_contra h2
    push_neg at h2
    have h3 : (a - b) ^ 2 ≥ 0 := by apply sq_nonneg
    have h4 : (a - c) ^ 2 ≥ 0 := by apply sq_nonneg
    have h5 : (b - c) ^ 2 ≥ 0 := by apply sq_nonneg
    have h6 : (a - b) ^ 2 = 0 := by linarith
    have h7 : (a - c) ^ 2 = 0 := by linarith
    have h8 : (b - c) ^ 2 = 0 := by linarith
    have h9 : a = b := by
      nlinarith
    have h10 : a = c := by
      nlinarith
    have h11 : b = c := by
      linarith
    have h12 : a = b ∧ b = c := by
      constructor
      · linarith
      · linarith
    contradiction
  have h3 : (a^2 + b^2 + c^2) > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_pos_of_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) ]
  have h4 : (a + b + c) ^2 < 3 * (a^2 + b^2 + c^2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h1]
  nlinarith [sq_nonneg ((a^2 + b^2 + c^2) * x + (a + b + c)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num) ]