import Mathlib

theorem algebra_252844 (a b : ℝ) :
    a^2 + b^2 ≠ 0 ∧ a + (a + 8 * b) / (a ^ 2 + b ^ 2) = 2 ∧
    b + (8 * a - b) / (a ^ 2 + b ^ 2) = 0 ↔
    (a = -1 ∧ b = 2) ∨ (a = 3 ∧ b = -2) := by
  constructor
  · -- Assume the equations hold, prove (a, b) is either (-1, 2) or (3, -2).
    rintro ⟨ha1, heq1, heq2⟩
    have h1 : a ^ 2 + b ^ 2 ≠ 0 := ha1
    have eq1' : a * (a ^ 2 + b ^ 2) + (a + 8 * b) = 2 * (a ^ 2 + b ^ 2) := by
      have eq1 : a + (a + 8 * b) / (a ^ 2 + b ^ 2) = 2 := by
        linarith
      have eq1' : a * (a ^ 2 + b ^ 2) + (a + 8 * b) = 2 * (a ^ 2 + b ^ 2) := by
        have eq2 : (a + (a + 8 * b) / (a ^ 2 + b ^ 2)) * (a ^ 2 + b ^ 2) = 2 * (a ^ 2 + b ^ 2) := by
          rw [eq1]
        have eq3 : (a + (a + 8 * b) / (a ^ 2 + b ^ 2)) * (a ^ 2 + b ^ 2) = a * (a ^ 2 + b ^ 2) + (a + 8 * b) := by
          field_simp [show a ^ 2 + b ^ 2 ≠ 0 by assumption]
          <;> ring
        rw [eq3] at eq2
        linarith
      linarith
    -- Second equation.
    have eq2' : b * (a ^ 2 + b ^ 2) + (8 * a - b) = 0 := by
      have eq2 : b + (8 * a - b) / (a ^ 2 + b ^ 2) = 0 := by
        linarith
      have eq2' : b * (a ^ 2 + b ^ 2) + (8 * a - b) = 0 := by
        have eq4 : (b + (8 * a - b) / (a ^ 2 + b ^ 2)) * (a ^ 2 + b ^ 2) = 0 * (a ^ 2 + b ^ 2) := by
          rw [eq2]
        have eq3 : (b + (8 * a - b) / (a ^ 2 + b ^ 2)) * (a ^ 2 + b ^ 2) = b * (a ^ 2 + b ^ 2) + (8 * a - b) := by
          field_simp [show a ^ 2 + b ^ 2 ≠ 0 by assumption]
          <;> ring
        rw [eq3] at eq4
        linarith
      linarith
    -- Now to solve the system.
    have eq3 : (a + 1) * (a - 3) = 0 := by
      nlinarith [sq_nonneg (a - b + 1), sq_nonneg (a + b - 1), sq_pos_of_ne_zero (show a ^ 2 + b ^ 2 ≠ 0 by assumption), sq_nonneg (a - 3), sq_nonneg (b - 2), sq_nonneg (a + 1), sq_nonneg (b + 2)]
    cases' (mul_eq_zero.mp eq3) with h4 h5
    · -- When a = -1.
      have ha2 : a = -1 := by linarith
      have hb2 : b = 2 := by
        rw [ha2] at eq1' eq2'
        nlinarith [sq_nonneg (b - 2), sq_nonneg (b + 2)]
      left
      exact ⟨ha2, hb2⟩
    · -- When a = 3.
      have ha3 : a = 3 := by linarith
      have hb3 : b = -2 := by
        rw [ha3] at eq1' eq2'
        nlinarith [sq_nonneg (b - 2), sq_nonneg (b + 2)]
      right
      exact ⟨ha3, hb3⟩
  · -- Assume (a, b) is either (-1, 2) or (3, -2). Prove the equations hold.
    rintro (h | h)
    · -- Case (-1, 2).
      rcases h with ⟨ha, hb⟩
      constructor
      · -- Show a^2 + b^2 ≠ 0.
        rw [ha, hb]
        norm_num
      constructor
      · -- Show a + (a + 8 * b) / (a ^ 2 + b ^ 2) = 2.
        rw [ha, hb]
        norm_num
      · -- Show b + (8 * a - b) / (a ^ 2 + b ^ 2) = 0.
        rw [ha, hb]
        norm_num
    · -- Case (3, -2).
      rcases h with ⟨ha, hb⟩
      constructor
      · -- Show a^2 + b^2 ≠ 0.
        rw [ha, hb]
        norm_num
      constructor
      · -- Show a + (a + 8 * b) / (a ^ 2 + b ^ 2) = 2.
        rw [ha, hb]
        norm_num
      · -- Show b + (8 * a - b) / (a ^ 2 + b ^ 2) = 0.
        rw [ha, hb]
        norm_num