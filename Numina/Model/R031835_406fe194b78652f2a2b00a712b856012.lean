import Mathlib

theorem algebra_228019 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (x + 2) ^ 2 / y + (y + 2) ^ 2 / x = 16) : x + y = 4 := by
  have h1 : x * y > 0 := by
    nlinarith 
  have h2 : (x + 2) ^ 2 * x + (y + 2) ^ 2 * y = 16 * (x * y) := by 
    have h11 : (x + 2) ^ 2 / y + (y + 2) ^ 2 / x = ( (x + 2) ^ 2 * x + (y + 2) ^ 2 * y ) / (x * y) := by 
      field_simp
      <;> ring_nf <;> field_simp <;> tauto 
    rw [h11] at h 
    field_simp at h ⊢
    <;> nlinarith
  have h_eq : (x + y - 4) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), 
      sq_nonneg (x + y - 4), 
      sq_pos_of_pos hx, sq_pos_of_pos hy, 
      mul_pos hx hy, 
      pow_two_nonneg (x - y), pow_two_nonneg (x + y - 4)]
  have h_eq2 : x + y - 4 = 0 := by
    have h_eq22 : (x + y -4) ^ 2 =0 := h_eq
    have h_eq33 : x + y -4 =0 := by
      nlinarith 
    exact h_eq33

  linarith 
  all_goals nlinarith