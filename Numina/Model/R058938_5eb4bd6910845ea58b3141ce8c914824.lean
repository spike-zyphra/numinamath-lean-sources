import Mathlib

theorem algebra_1572 {a b : ℝ} (h : a ^ 2 + b ^ 2 + a ^ 2 * b ^ 2 = 4 * a * b - 1) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  have h1 : (a - 1) ^ 2 + (b - 1) ^ 2 ≥ 0 := by 
    linarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]
  have h2 : (a + 1) ^ 2 + (b + 1) ^ 2 ≥ 0 := by 
    linarith [sq_nonneg (a + 1), sq_nonneg (b + 1)]
  have h3 : (a - b) ^ 2 + (a * b - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b - 1)]
  have h4 : (a - b) ^ 2 = 0 := by
    linarith [sq_nonneg (a - b), sq_nonneg (a * b - 1)]
  have h5 : (a * b - 1) ^ 2 = 0 := by
    linarith [sq_nonneg (a - b), sq_nonneg (a * b - 1)]
  have h6 : a - b = 0 := by
    rwa [sq_eq_zero_iff] at h4
  have h7 : a * b - 1 = 0 := by
    rwa [sq_eq_zero_iff] at h5
  have h8 : a = b := by
    linarith 
  have h9 : a * a = 1 := by 
    have : a * b = 1 := by 
      nlinarith 
    rw [show b = a by linarith [h8]] at this 
    nlinarith 
  have ha : (a = 1) ∨ (a = -1) := by 
    have h10 : a ^ 2 = 1 := by 
      nlinarith 
    have h11 : (a - 1) * (a + 1) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp h11) with h12 h13 
    · left
      linarith 
    · right 
      linarith 
  cases ha with
  | inl ha1 =>
    have hb1 : b = 1 := by 
      nlinarith [show a = b by linarith [h8]]
    left
    exact ⟨ha1, hb1⟩
  | inr ha2 =>
    have hb2 : b = -1 := by 
      nlinarith [show a = b by linarith [h8]]
    right
    exact ⟨ha2, hb2⟩