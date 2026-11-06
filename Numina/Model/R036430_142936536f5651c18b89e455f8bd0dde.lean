import Mathlib
theorem algebra_605458 (a b c d : ℝ) : a = b * c + c * d ∧ b = c * d + d * a ∧ c = d * a + a * b ∧ d = a * b + b * c ↔
(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 1 / 2 ∧ d = 1 / 2) := by
  constructor
  · -- Assume the system of equations holds, prove the two solutions
    rintro ⟨ha, hb, hc, hd⟩
    have ha1 : a - b = 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b)]
    have ha2 : a - c = 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b)]
    have ha3 : a - d = 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b)]
    have ha4 : a = b := by linarith 
    have ha5 : a = c := by linarith 
    have ha6 : a = d := by linarith 
    have ha7 : a * (2 * a - 1) = 0 := by
      have h_eq1 : d = a := by linarith 
      rw [show b = a by linarith, show c = a by linarith, show d = a by linarith] at ha 
      nlinarith 
    cases' (mul_eq_zero.mp ha7) with h10 h11
    · -- a = 0 
      have ha0 : a = 0 := h10
      have hb0 : b = 0 := by linarith 
      have hc0 : c = 0 := by linarith 
      have hd0 : d = 0 := by linarith 
      left 
      exact ⟨ha0, hb0, hc0, hd0⟩
    · -- 2a - 1 = 0
      have ha1 : a = 1 / 2 := by linarith 
      have hb1 : b = 1 / 2 := by linarith [ha4, ha1]
      have hc1 : c = 1 / 2 := by linarith [ha5, ha1]
      have hd1 : d = 1 / 2 := by linarith [ha6, ha1]
      right
      exact ⟨ha1, hb1, hc1, hd1⟩ 
  · -- Show that the two solutions satisfy the system
    rintro (h | h)
    · -- Case where all variables are zero
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
      constructor
      · norm_num
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- Case where all variables are 1/2 
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num