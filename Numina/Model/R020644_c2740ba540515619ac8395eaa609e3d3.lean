import Mathlib

theorem algebra_321919 (a b c : ℝ) (h : ¬(a = c ∧ c = b)) :
    ¬∃ x : ℝ, x^2 + (a + b + c) * x + (a^2 + b^2 + c^2) = 0 := by
  rintro ⟨x, hx⟩
  have h1 : (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 > 0 := by
    by_contra h2
    push_neg at h2
    have h21 : (a - b) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h2]
    have h22 : (a - c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h2]
    have h23 : (b - c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h2]
    have h_eq1 : a - b = 0 := by
      nlinarith [h21]
    have h_eq2 : a - c = 0 := by 
      nlinarith [h22]
    have h_eq3 : b - c = 0 := by
      nlinarith [h23]
    have h_eq4 : a = b := by 
      linarith
    have h_eq5 : a = c := by 
      linarith
    have h_eq6 : b = c := by 
      linarith
    have h7 : a = c ∧ c = b := by
      constructor
      · linarith
      · linarith
    contradiction 
  have h2 : (a + b + c) ^ 2 < 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by 
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h1]
  have h4 : (2 * x + (a + b + c)) ^ 2 < 0 := by
    nlinarith [sq_nonneg (2 * x + (a + b + c)), sq_nonneg (x), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  nlinarith [sq_nonneg (2 * x + (a + b + c))]