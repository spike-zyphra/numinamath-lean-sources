import Mathlib

theorem algebra_256961 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 2 * x ^ 2 + 2 * y ^ 2 = 5 * x * y) :
    (x + y) / (x - y) = 3 ∨ (x + y) / (x - y) = -3 := by
  have h1 : (x + y) ^ 2 = 9 * ((x - y) ^ 2) := by
    have h2 : x ^ 2 + y ^ 2 = (5 / 2) * x * y := by
      nlinarith
    nlinarith [h2, sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_nonneg (x - y), sq_nonneg (x + y)]
    
  have h4 : x - y ≠ 0 := by
    by_contra h4
    have h5 : x = y := by linarith
    rw [show y = x by linarith [h5]] at h
    have h6 : 2 * x ^ 2 + 2 * x ^ 2 = 5 * x * x := by
      linarith
    have h7 : x ^ 2 = 0 := by
      nlinarith
    have h8 : x = 0 := by
      nlinarith
    contradiction

  have h5 : ((x + y) / (x - y)) ^ 2 = 9 := by
    have h6 : (x - y) ≠ 0 := h4
    have h7 : (x - y) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      exact h4
    have h8 : (x + y) ^ 2 = 9 * ((x - y) ^ 2) := h1
    have h9 : ((x + y) / (x - y)) ^ 2 = ((x + y) ^ 2) / ((x - y) ^ 2) := by
      field_simp
    rw [h9]
    have h10 : (x + y) ^ 2 = 9 * ((x - y) ^ 2) := h8
    field_simp
    nlinarith
  
  have h6 : (x + y) / (x - y) = 3 ∨ (x + y) / (x - y) = -3 := by
    have h7 : ((x + y) / (x - y)) ^ 2 = 9 := h5
    have h8 : ( (x + y) / (x - y) - 3) * ( (x + y) / (x - y) + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h8) with
    | inl h9 =>
      left
      linarith
    | inr h10 =>
      right
      linarith
  
  exact h6