import Mathlib

theorem algebra_198526 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + x / y = 8 / 3) (h2 : y - 1 / x = 5 / 2) :
    (x, y) = (2, 3) ∨ (x, y) = (-8 / 21, -1 / 8) := by 
  have eq1 : 3 * x * y + 3 * x - 8 * y = 0 := by
    have h1' : x + x / y = 8 / 3 := h1
    have h11 : x * y + x = (8 / 3) * y := by 
      have h12 : x + x / y = 8 / 3 := h1
      field_simp [hy] at h12 ⊢ 
      nlinarith
    nlinarith [h11]
  have eq2 : 2 * x * y - 5 * x - 2 = 0 := by 
    have h2' : y - 1 / x = 5 / 2 := h2
    have h21 : y * x - 1 = (5 / 2) * x := by 
      have h22 : y - 1 / x = 5 / 2 := h2
      field_simp [hx] at h22 ⊢ 
      nlinarith [h22]
    nlinarith [h21]
  have h3 : (x - 2) * (x + 8 / 21) = 0 := by 
    nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x + 8 / 21), sq_nonneg (y + 1 / 8)]
  cases (mul_eq_zero.mp h3) with
  | inl h31 =>
    have hx2 : x = 2 := by linarith
    have hy3 : y = 3 := by 
      rw [hx2] at eq2
      nlinarith
    left 
    simp [hx2, hy3]
  | inr h32 =>
    have hx8 : x = -8 / 21 := by linarith
    have hy18 : y = -1 / 8 := by 
      rw [hx8] at eq2
      nlinarith
    right 
    simp [hx8, hy18]