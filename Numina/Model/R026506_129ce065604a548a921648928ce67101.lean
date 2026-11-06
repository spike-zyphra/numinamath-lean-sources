import Mathlib

theorem algebra_138733 {a b : ℝ} (h₀ : abs a ≠ abs b) (h₁ : (a + b) / (a - b) + (a - b) / (a + b) = 6) :
    (a ^ 3 + b ^ 3) / (a ^ 3 - b ^ 3) + (a ^ 3 - b ^ 3) / (a ^ 3 + b ^ 3) = 18 / 7 := by
  have h2 : a - b ≠ 0 := by
    by_contra h
    have h3 : a = b := by linarith
    have h4 : abs a = abs b := by
      rw [show b = a by linarith [h3]]
    tauto
  have h3 : a + b ≠ 0 := by
    by_contra h
    have h4 : a = -b := by linarith
    have h5 : abs a = abs b := by
      rw [show a = -b by linarith [h4]]
      simp [abs_neg]
    tauto
  have eq1 : (a + b) ^ 2 + (a - b) ^ 2 = 6 * (a - b) * (a + b) := by
    have eq2 : (a + b) / (a - b) + (a - b) / (a + b) = 6 := h₁
    have eq3 : (a + b) / (a - b) + (a - b) / (a + b) =
        ((a + b) ^ 2 + (a - b) ^ 2) / ((a - b) * (a + b)) := by
      field_simp [h2, h3]
      <;> ring
    rw [eq3] at eq2
    have eq4 : (a - b) * (a + b) ≠ 0 := by
      apply mul_ne_zero
      exact h2
      exact h3
    field_simp [eq4] at eq2 ⊢
    linarith
  have eq2 : a ^ 2 = 2 * b ^ 2 := by
    nlinarith [eq1]
  by_cases h5 : b = 0
  · -- Assume b = 0, we show a contradiction
    have h6 : a = 0 := by
      rw [h5] at eq2
      nlinarith
    have h7 : abs a = abs b := by
      rw [h6, h5]
      all_goals
        simp
    tauto
  · -- Assume b ≠ 0
    have h4' : a ≠ 0 := by
      by_contra h
      have h8 : b = 0 := by
        nlinarith [eq2, h]
      tauto
    have hb1 : a ^ 3 - b ^ 3 ≠ 0 := by
      by_contra h
      have h6 : a ^ 3 = b ^ 3 := by linarith
      have h7 : a = b := by
        have h8 : a ^ 3 - b ^ 3 = 0 := by linarith [h6]
        have h9 : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h9) with h10 h11
        · -- h10 : a - b = 0
          linarith
        · -- h11 : a ^ 2 + a * b + b ^ 2 = 0
          have h14 : a ^ 2 = 2 * b ^ 2 := eq2
          nlinarith [sq_nonneg (a - b), sq_pos_of_ne_zero (show b ≠ 0 by assumption)]
      -- This would lead to a = b, which contradicts $|a| \neq |b|$.
      have h4 : abs a = abs b := by
        rw [show b = a by linarith [h7]]
      tauto
    have hb2 : a ^ 3 + b ^ 3 ≠ 0 := by
      by_contra h
      have  h6 : a ^ 3 = -b ^ 3 := by linarith
      -- This gives a = -b, contradicting |a| ≠ |b|.
      have h7 : a = -b := by
        have h8 : a ^ 3 + b ^ 3 = 0 := by linarith [h6]
        have h9 : (a + b) * (a ^ 2 - a * b + b ^ 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h9) with h10 h11
        · -- h10 : a + b = 0
          linarith
        · -- h11 : a ^ 2 - a * b + b ^ 2 = 0
          have h14 : a ^ 2 = 2 * b ^ 2 := eq2
          nlinarith [sq_nonneg (a + b), sq_pos_of_ne_zero (show b ≠ 0 by assumption)]
      have h4 : abs a = abs b := by
        rw [show a = -b by linarith [h7]]
        simp [abs_neg]
      tauto
    field_simp [hb1, hb2]
    nlinarith [sq_nonneg (a ^ 2 - 2 * b ^ 2), sq_nonneg (a * b), sq_nonneg (a ^ 2 + b ^ 2), sq_pos_of_ne_zero (show b ^ 2 ≠ 0 by
      apply pow_ne_zero 2
      assumption
    )]