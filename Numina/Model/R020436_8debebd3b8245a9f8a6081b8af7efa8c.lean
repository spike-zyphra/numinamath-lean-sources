import Mathlib

theorem algebra_147197 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : a ≠ b) (h : a^3 + b^3 = (a + b)^2) :
    a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1 := by
  have h5 : a ≤ 3 := by
    by_contra h2
    push_neg at h2
    have h7 : a ≥ 4 := by omega
    have h4 : b < a := by
      nlinarith [sq_pos_of_pos (show 0 < a by omega), sq_pos_of_pos (show 0 < b by omega), 
        pow_pos (show 0 < a by omega) 3, pow_pos (show 0 < b by omega) 3, h, 
        sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2)]
    have h5 : b ≤ a := by omega
    -- Now with b <= a
    nlinarith [sq_pos_of_pos (show 0 < a by omega), sq_pos_of_pos (show 0 < b by omega), 
      pow_pos (show 0 < a by omega) 3, pow_pos (show 0 < b by omega) 3, h, 
      sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2)]
  have h5 : a ≤ 3 := h5
  have h5 : b ≤ 6 := by
    nlinarith [sq_pos_of_pos (show 0 < a by omega), sq_pos_of_pos (show 0 < b by omega), 
      pow_pos (show 0 < a by omega) 3, pow_pos (show 0 < b by omega) 3, h, 
      sq_nonneg (a - 3), sq_nonneg (b - 3)]
  interval_cases a <;> interval_cases b
  <;> omega