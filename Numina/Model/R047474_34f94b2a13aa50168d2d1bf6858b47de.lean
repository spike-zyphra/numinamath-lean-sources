import Mathlib

theorem algebra_243349 {a b : ℝ} (h : a ≠ 0 ∧ b ≠ 0 ∧ a + b = 1) :
    a / (b ^ 3 - 1) - b / (a ^ 3 - 1) = 2 * (b - a) / (a ^ 2 * b ^ 2 + 3) := by 
  rcases h with ⟨ha, hb, hsum⟩
  have h1 : b = 1 - a := by 
    linarith
  have h3 : (1 - a) ≠ 0 := by 
    intro h4
    have h5 : b = 0 := by
      rw [h1]
      linarith
    contradiction
  rw [h1]
  have h4 : a ≠ 0 := ha
  have h5 : (1 - a) ≠ 0 := h3
  have h6 : a ^ 3 - 1 ≠ 0 := by 
    intro h7
    have h7' : a = 1 := by 
      have h8 : a ^ 3 - 1 = 0 := h7
      have h9 : a^3 - 1 = (a - 1) * (a^2 + a + 1) := by ring
      rw [h9] at h8
      cases' (mul_eq_zero.mp h8) with h10 h11
      · -- h10 : a - 1 = 0
        linarith
      · -- h11 : a^2 + a + 1 = 0
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero (show (1 - a) ≠ 0 by assumption)]
    have h6a : (1 - a) = 0 := by linarith
    contradiction
  have h7 : (1 - a) ^ 3 - 1 ≠ 0 := by 
    intro h7
    have h8 : (1 - a) = 1 := by 
      have h9 : (1 - a) ^ 3 - 1 = 0 := by linarith
      have h10 : ((1 - a) - 1) * ((1 - a) ^ 2 + (1 - a) + 1) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- h11 : (1 - a) - 1 = 0
        linarith
      · -- h12 : (1 - a)^2 + (1 - a) + 1 = 0
        nlinarith [sq_pos_of_ne_zero (show (1 - a) ≠ 0 by assumption), sq_pos_of_ne_zero h4]
    have h6a : a = 0 := by linarith
    contradiction
  have h8 : a ^ 2 * (1 - a) ^ 2 + 3 ≠ 0 := by 
    nlinarith [sq_pos_of_ne_zero h4, sq_pos_of_ne_zero (show (1 - a) ≠ 0 by assumption)]
  field_simp [h4, h5, h6, h7, h8]
  <;> nlinarith [sq_pos_of_ne_zero h4, sq_pos_of_ne_zero (show (1 - a) ≠ 0 by assumption), 
    sq_nonneg (a - 1), sq_nonneg (a - (1 - a)), sq_nonneg (a^2 - (1 - a)^2), sq_nonneg (a * (1 - a))]