import Mathlib

theorem inequalities_260718 (x y : ℝ) (hx : x ≠ -1) (hy : y ≠ -1) (hxy : x * y = 1) :
    (9 / 2) ≤ ((2 + x) / (1 + x)) ^ 2 + ((2 + y) / (1 + y)) ^ 2 := by 
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hy1 : 1 + y ≠ 0 := by
    intro h
    apply hy
    linarith
  have h1 : ((2 + x) / (1 + x)) ^ 2 + ((2 + y) / (1 + y)) ^ 2 - 9 / 2 ≥ 0 := by
    have h2 : ((2 + x) / (1 + x)) ^ 2 + ((2 + y) / (1 + y)) ^ 2 - 9 / 2 =
          (2 * (2 + x) ^ 2 * (1 + y) ^ 2 + 2 * (2 + y) ^ 2 * (1 + x) ^ 2 - 9 * (1 + x) ^ 2 * (1 + y) ^ 2) / (2 * (1 + x) ^ 2 * (1 + y) ^ 2) := by
      field_simp
      ring
    rw [h2] at *
    have h3 : 2 * (2 + x) ^ 2 * (1 + y) ^ 2 + 2 * (2 + y) ^ 2 * (1 + x) ^ 2 - 9 * (1 + x) ^ 2 * (1 + y) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + 1), sq_nonneg (y + 1),
          sq_nonneg (x * y - 1), hxy, sq_nonneg (x - y), sq_nonneg (x + y - 2)]
    have h3' : (2 * (1 + x) ^ 2 * (1 + y) ^ 2) > 0 := by
      have h4 : (1 + x) ≠ 0 := hx1
      have h5 : (1 + y) ≠ 0 := hy1
      have h6 : (1 + x) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        exact h4
      have h7 : (1 + y) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        exact h5
      positivity
    apply div_nonneg 
    linarith 
    positivity
  linarith