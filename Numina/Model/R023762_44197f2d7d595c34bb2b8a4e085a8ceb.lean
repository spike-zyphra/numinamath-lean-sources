import Mathlib

theorem algebra_1255 (x : ℝ) (hx1 : x^2 - 7 * x + 12 ≠ 0) (hx2 : x^2 - 2 * x - 3 ≠ 0) (hx3 : x^2 - 3 * x - 4 ≠ 0) :
    (x - 5) / (x^2 - 7 * x + 12) = (x + 5) / (x^2 - 2 * x - 3) + (x - 3) / (x^2 - 3 * x - 4) ↔ x = -2 := by
  constructor
  · -- Assume the equation holds, prove x = -2
    intro h_eq
    have h1 : x^2 - 7 * x + 12 ≠ 0 := hx1
    have h2 : x^2 - 2 * x - 3 ≠ 0 := hx2
    have h3 : x^2 - 3 * x - 4 ≠ 0 := hx3
    have h4 : x - 3 ≠ 0 := by
      intro h5
      have h1' : x^2 - 7 * x + 12 = 0 := by
        have h11 : x = 3 := by linarith
        rw [h11]
        norm_num
      contradiction
    have h5 : x - 4 ≠ 0 := by
      intro h6
      have h1' : x^2 - 7 * x + 12 = 0 := by
        have h11 : x = 4 := by linarith
        rw [h11]
        norm_num
      contradiction
    have h6 : x + 1 ≠ 0 := by
      intro h7
      have h2' : x^2 - 2 * x - 3 = 0 := by
        have h22 : x = -1 := by linarith
        rw [h22]
        norm_num
      contradiction
    have eq1 : (x + 2) * (x - 3) = 0 := by
      have eq2 : (x - 5) * (x^2 - 2 * x - 3) * (x^2 - 3 * x - 4) - ((x + 5) * (x^2 - 7 * x + 12) * (x^2 - 3 * x - 4) + (x - 3) * (x^2 - 7 * x + 12) * (x^2 - 2 * x - 3)) = 0 := by
        have h7 : (x - 5) / (x^2 - 7 * x + 12) = (x + 5) / (x^2 - 2 * x - 3) + (x - 3) / (x^2 - 3 * x - 4) := h_eq
        have eq3 : (x - 5) / (x^2 - 7 * x + 12) - ((x + 5) / (x^2 - 2 * x - 3) + (x - 3) / (x^2 - 3 * x - 4)) = 0 := by linarith
        have hx1' : x^2 - 7 * x + 12 ≠ 0 := hx1
        have hx2' : x^2 - 2 * x - 3 ≠ 0 := hx2
        have hx3' : x^2 - 3 * x - 4 ≠ 0 := hx3
        field_simp [(show x^2 - 7 * x + 12 ≠ 0 by assumption), 
          (show x^2 - 2 * x - 3 ≠ 0 by assumption), 
          (show x^2 - 3 * x - 4 ≠ 0 by assumption), 
          h4, h5, h6] at eq3 ⊢
        nlinarith
      nlinarith [sq_pos_of_ne_zero (show x^2 - 7 * x + 12 ≠ 0 by assumption), sq_pos_of_ne_zero (show x^2 - 2 * x - 3 ≠ 0 by assumption), sq_pos_of_ne_zero (show x^2 - 3 * x - 4 ≠ 0 by assumption), sq_nonneg (x + 2), sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x - 4), h4, h5, h6]
    have h8 : x + 2 = 0 ∨ x - 3 = 0 := by
      cases (mul_eq_zero.1 eq1) with
      | inl h8 => 
        left
        linarith
      | inr h8 => 
        right
        linarith
    cases h8 with
    | inl h9 => 
      linarith
    | inr h10 => 
      exfalso
      have h11 : x = 3 := by linarith
      have h12 : x^2 - 7 * x + 12 = 0 := by
        rw [h11]
        norm_num
      contradiction
  · -- Assume x = -2, prove the equation holds
    intro h_eq
    rw [h_eq]
    norm_num