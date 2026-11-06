import Mathlib

theorem algebra_299297 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + y + 9 / x + 4 / y = 10) (h2 : (x ^ 2 + 9) * (y ^ 2 + 4) = 24 * x * y) :
    x = 3 ∧ y = 2 := by
  have h3 : (x + 9 / x) + (y + 4 / y) = 10 := by 
    linarith [h1]
  have h4 : (x + 9 / x) * (y + 4 / y) = 24 := by
    have eq1 : (x + 9 / x) * (y + 4 / y) = ((x ^ 2 + 9) * (y ^ 2 + 4)) / (x * y) := by
      field_simp [hx, hy]
      <;> ring_nf
      <;> field_simp [hx, hy]
      <;> nlinarith
      <;> ring_nf
    have eq2 : (x ^ 2 + 9) * (y ^ 2 + 4) = 24 * x * y := by 
      nlinarith [h2, sq_nonneg (x * y), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
    rw [eq1]
    rw [eq2]
    field_simp [hx, hy]
    <;> nlinarith
  have h5 : (x + 9 / x) ^ 2 - 10 * (x + 9 / x) + 24 = 0 := by
    nlinarith [h3, h4, sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_nonneg (x + 9 / x - 4), sq_nonneg (y + 4 / y - 6), sq_nonneg (x + 9 / x - 6), sq_nonneg (y + 4 / y - 4)]
  have h6 : ((x + 9 / x) - 6) * ((x + 9 / x) - 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where (x + 9 / x) = 6
    have hx_eq : x + 9 / x = 6 := by
      linarith
    have h7' : x ^ 2 - 6 * x + 9 = 0 := by
      field_simp [hx] at hx_eq
      nlinarith
    have hx_eq2 : (x - 3) ^ 2 = 0 := by
      nlinarith
    have hx_eq3 : x - 3 = 0 := by
      apply pow_eq_zero 
      exact hx_eq2
    have hx_eq3 : x = 3 := by linarith
    have hy_eq : y + 4 / y = 4 := by
      linarith [h3, hx_eq]
    have h7' : y ^ 2 - 4 * y + 4 = 0 := by
      field_simp [hy] at hy_eq
      nlinarith
    have hy_eq2 : (y - 2) ^ 2 = 0 := by
      nlinarith
    have hy_eq3 : y - 2 = 0 := by
      apply pow_eq_zero 
      exact hy_eq2
    have hy_eq3 : y = 2 := by linarith
    exact ⟨hx_eq3, hy_eq3⟩
  · -- Case where (x + 9 / x) = 4
    have hx_eq : x + 9 / x = 4 := by
      linarith
    have h7' : x ^ 2 - 4 * x + 9 = 0 := by
      field_simp [hx] at hx_eq
      nlinarith
    nlinarith [sq_pos_of_ne_zero (show (x) ≠ 0 by assumption), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x - 3), sq_nonneg (y - 2)]