import Mathlib

theorem algebra_285286 {x : ℝ} (hx : x ≠ 0) :
    x^2 + 1 / x^2 = 2006 + 1 / 2006 ↔
    x = √2006 ∨ x = -√2006 ∨ x = √2006 / 2006 ∨ x = -√2006 / 2006 := by
  constructor
  · -- Assume x^2 + 1/x^2 = 2006 + 1/2006, prove the four possible roots
    intro h
    have h1 : x^4 + 1 = (2006 + 1 / 2006) * x^2 := by
      have h2 : x^2 + 1 / x^2 = 2006 + 1 / 2006 := h
      field_simp [hx] at h2 ⊢
      nlinarith [sq_pos_of_ne_zero hx]
    have h2 : (x^2 - 2006) * (x^2 - 1 / 2006) = 0 := by
      nlinarith [sq_nonneg (x^2 - 2006), sq_nonneg (x^2 - 1 / 2006), sq_pos_of_pos (show (0 : ℝ) < 2006 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- When x^2 = 2006
      have h5 : x^2 = 2006 := by linarith
      have h8 : x = Real.sqrt 2006 ∨ x = - Real.sqrt 2006 := by
        have h9 : x^2 = (Real.sqrt 2006) ^ 2 := by
          rw [h5]
          rw [Real.sq_sqrt]
          all_goals norm_num
        have : x = Real.sqrt 2006 ∨ x = - Real.sqrt 2006 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          linarith
        assumption
      cases h8 with
      | inl h9 =>
        left
        linarith [h9]
      | inr h11 =>
        right
        left
        linarith [h11]
    · -- When x^2 = 1 / 2006
      have h8 : x^2 = 1 / 2006 := by linarith
      have h10 : x = Real.sqrt (1 / 2006) ∨ x = - Real.sqrt (1 / 2006) := by
        have h9 : x^2 = (Real.sqrt (1 / 2006)) ^ 2 := by
          rw [h8]
          rw [Real.sq_sqrt]
          all_goals norm_num
        have : x = Real.sqrt (1 / 2006) ∨ x = - Real.sqrt (1 / 2006) := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          linarith
        assumption
      cases h10 with
      | inl h11 =>
        have h12 : Real.sqrt (1 / 2006) = Real.sqrt 2006 / 2006 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h12] at h11
        right
        right
        left
        linarith [h11]
      | inr h13 =>
        have h14 : -Real.sqrt (1 / 2006) = - (Real.sqrt 2006 / 2006) := by
          have h15 : Real.sqrt (1 / 2006) = Real.sqrt 2006 / 2006 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf <;> norm_num
          linarith [h15]
        rw [h14] at h13
        right
        right
        right
        linarith [h13]
  · -- Assume x is one of the four roots, prove the equation
    rintro (h | h | h | h)
    · -- When x = √2006
      rw [h]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (2006 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2006 by norm_num)]
    · -- When x = -√2006
      rw [h]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (2006 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2006 by norm_num)]
    · -- When x = √2006 / 2006
      rw [h]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (2006 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2006 by norm_num)]
    · -- When x = -√2006 / 2006
      rw [h]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (2006 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2006 by norm_num)]