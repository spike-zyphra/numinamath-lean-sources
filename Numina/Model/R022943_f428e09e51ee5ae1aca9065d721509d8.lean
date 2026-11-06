import Mathlib

theorem algebra_325978 (x : ℝ) (hx : x ≠ 0) :
    16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) = Real.sin (Real.pi * x) ↔ x = 1 / 2 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 1/2
    intro h_eq
    have h1 : 16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) ≥ 1 := by
      have h2 : x ^ 2 > 0 := by
        exact sq_pos_of_ne_zero hx
      have h4 : 6 * x ^ 2 > 0 := by
        nlinarith
      have h3 : 16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) - 1 ≥ 0 := by
        have h5 : 16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) - 1 = (32 * x ^ 6 - 6 * x ^ 2 + 1) / (6 * x ^ 2) := by
          field_simp
          ring
        have h6 : 32 * x ^ 6 - 6 * x ^ 2 + 1 ≥ 0 := by
          nlinarith [sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2 + 1 / 2), sq_nonneg (x ^ 2 - 1 / 2), sq_nonneg (x * 2), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x * 4)]
        have h7 : (32 * x ^ 6 - 6 * x ^ 2 + 1) / (6 * x ^ 2) ≥ 0 := by
          apply div_nonneg
          linarith
          nlinarith
        linarith [h5, h7]
      linarith
    have h2 : Real.sin (Real.pi * x) ≤ 1 := by
      apply Real.sin_le_one
    have h3 : 16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) = 1 := by
      nlinarith [h1, h2, h_eq]
    have h4 : x ^ 2 = 1 / 4 := by
      have h5 : 16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) = 1 := h3
      have h6 : x ^ 2 > 0 := by
        exact sq_pos_of_ne_zero hx
      have h7 : 6 * x ^ 2 > 0 := by
        nlinarith
      have h8 : 32 * x  ^ 6 - 6 * x ^ 2 + 1 = 0 := by
        have h9 : (16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) - 1) = 0 := by linarith
        have h10 : (16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) - 1) = (32 * x ^ 6 - 6 * x ^ 2 + 1) / (6 * x ^ 2) := by
          field_simp
          ring
        rw [h10] at h9
        field_simp at h9 ⊢
        nlinarith [sq_pos_of_pos h6]
      nlinarith [sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2 + 1 / 2), sq_nonneg (x ^ 2 - 1 / 2), sq_pos_of_pos h6]
    have hx1 : x = 1 / 2 ∨ x = -1 / 2 := by
      have h8 : x ^ 2 = 1 / 4 := h4
      have : x = 1 / 2 ∨ x = -1 / 2 := by
        have h9 : x ^ 2 - (1 / 4) = 0 := by linarith
        have h10 : (x - 1 / 2) * (x + 1 / 2) = 0 := by
          nlinarith
        cases (mul_eq_zero.1 h10) with
        | inl h11 =>
          left
          linarith
        | inr h12 =>
          right
          linarith
      assumption
    cases hx1 with
    | inl h9 =>
      tauto
    | inr h9 =>
      -- Show that x = -1/2 is not a solution
      have h5 : Real.sin (Real.pi * x) = -1 := by
        rw [show x = -1 / 2 by linarith]
        have h10 : Real.sin (Real.pi * (-1 / 2 : ℝ)) = -1 := by 
          have : Real.pi * (-1 / 2 : ℝ) = - (Real.pi / 2) := by ring
          rw [this]
          have h11 : Real.sin (- (Real.pi / 2)) = - Real.sin (Real.pi / 2) := by 
            rw [Real.sin_neg]
          rw [h11]
          have h12 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
          nlinarith
        linarith
      nlinarith [h5, h3]
  · -- Backward direction: x = 1/2 then equation holds
    intro h_eq
    rw [h_eq]
    have h1 : 16 / 3 * ( (1 / 2 : ℝ) ) ^ 4 + 1 / (6 * ( (1 / 2 : ℝ) ) ^ 2) = 1 := by
      norm_num
    have h2 : Real.sin (Real.pi * ( (1 / 2 : ℝ) ) ) = 1 := by
      have h3 : Real.sin (Real.pi * ( (1 / 2 : ℝ) ) ) = Real.sin (Real.pi / 2) := by
        ring_nf
      rw [h3]
      exact Real.sin_pi_div_two
    linarith [h1, h2]