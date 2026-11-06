import Mathlib

theorem algebra_13204 (x y z w : ℝ)(xn0: x ≠ 0)(yn0: y ≠ 0)(zn0: z ≠ 0)(wn0: w ≠ 0)
(h: 1 + 1/x + 2*(x+1)/(x*y) + 3*(x+1)*(y+2)/(x*y*z) +
4*(x+1)*(y+2)*(z+3)/(x*y*z*w)= 0): x=-1 ∨ y=-2 ∨ z=-3 ∨ w=-4 := by 
  have h_eq : (x + 1) * (y + 2) * (z + 3) * (w + 4) = 0 := by
    have h1 : 1 + 1 / x + 2 * (x + 1) / (x * y) + 3 * (x + 1) * (y + 2) / (x * y * z) + 4 * (x + 1) * (y + 2) * (z + 3) / (x * y * z * w) = 0 := h
    have h2 : (x * y * z * w : ℝ) ≠ 0 := by 
      apply mul_ne_zero
      apply mul_ne_zero
      apply mul_ne_zero
      exact xn0
      exact yn0
      exact zn0
      exact wn0
    have h3 : (1 + 1 / x + 2 * (x + 1) / (x * y) + 3 * (x + 1) * (y + 2) / (x * y * z) + 4 * (x + 1) * (y + 2) * (z + 3) / (x * y * z * w)) * (x * y * z * w) = 0 := by 
      rw [h1]
      <;> norm_num
      <;> field_simp [xn0, yn0, zn0, wn0]
    have eq1 : (1 + 1 / x + 2 * (x + 1) / (x * y) + 3 * (x + 1) * (y + 2) / (x * y * z) + 4 * (x + 1) * (y + 2) * (z + 3) / (x * y * z * w)) * (x * y * z * w) = (x + 1) * (y + 2) * (z + 3) * (w + 4) := by
      field_simp [xn0, yn0, zn0, wn0]
      <;> ring
    rw [eq1] at h3
    linarith
  cases' (mul_eq_zero.mp h_eq) with h1 h2
  · cases' (mul_eq_zero.mp h1) with h1 h1
    · cases' (mul_eq_zero.mp h1) with h1 h1
      · left 
        linarith
      · right
        left
        linarith
    · right
      right
      left
      linarith
  · right
    right
    right
    linarith