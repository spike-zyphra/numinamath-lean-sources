import Mathlib

theorem algebra_238382 {x y : ℝ} (hx : x ≠ y) (h : 1/(x^2+1) + 1/(y^2+1) = 2/(x*y+1)) :
    1/(x^2+1) + 1/(y^2+1) + 2/(x*y+1) = 2 := by
  have h1 : x^2+1 ≠ 0 := by
    have h2 : x^2 ≥ 0 := sq_nonneg x
    linarith
  have h2' : y^2+1 ≠ 0 := by
    have h3 : y^2 ≥ 0 := sq_nonneg y
    linarith
  have h3 : x * y + 1 ≠ 0 := by 
    by_contra h4
    have h5 : 2 / (x * y + 1) = 0 := by
      rw [h4]
      norm_num
    have h6 : 1 / (x^2 + 1) + 1 / (y^2 + 1) = 0 := by 
      nlinarith [h, h5]
    have h7 : 1 / (x^2 + 1) > 0 := by
      apply div_pos
      norm_num
      nlinarith [sq_nonneg x]
    have h8 : 1 / (y^2 + 1) > 0 := by
      apply div_pos
      norm_num
      nlinarith [sq_nonneg y]
    linarith [h7, h8, h6]
  have h4 : (y^2 + 1) * (x * y + 1) + (x^2 + 1) * (x * y + 1) = 2 * (x^2 + 1) * (y^2 + 1) := by 
    have h5 : x^2 + 1 ≠ 0 := h1
    have h6 : y^2 + 1 ≠ 0 := h2'
    have h7 : x * y + 1 ≠ 0 := h3
    field_simp [h5, h6, h7] at h ⊢
    nlinarith
  have h5 : (x - y) * (x * y - 1) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h6
      apply hx
      linarith
    ), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1)]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Contradiction since x ≠ y
    exfalso
    apply hx
    linarith
  · -- Now, x * y = 1
    have h8 : x * y = 1 := by 
      linarith
    have h10 : 1 / (x^2 + 1) + 1 / (y^2 + 1) = 1 := by 
      have h9 : x * y + 1 = 2 := by
        nlinarith [h8]
      have h5 : 1 / (x^2 + 1) + 1 / (y^2 + 1) = 2 / (x * y + 1) := by 
        linarith [h]
      rw [h5]
      rw [h9]
      norm_num
    calc
      1 / (x^2 + 1) + 1 / (y^2 + 1) + 2 / (x * y + 1) = (1 / (x^2 + 1) + 1 / (y^2 + 1)) + 2 / (x * y + 1) := by ring
      _ = 1 + 2 / (x * y + 1) := by 
        rw [h10]
      _ = 1 + 2 / 2 := by 
        have h9 : x * y + 1 = 2 := by
          nlinarith [h8]
        rw [h9]
      _ = 1 + 1 := by 
        norm_num
      _ = 2 := by 
        norm_num