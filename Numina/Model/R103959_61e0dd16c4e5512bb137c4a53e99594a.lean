import Mathlib

theorem algebra_160138 {y : ℝ} (hy : y ≠ 0) :
    Real.sqrt ((y^2 + 4 / y^2)^2 - 8 * (y + 2 / y)^2 + 48) =
    (y - 2 / y)^2 := by
  have h1 : (y ^ 2 + 4 / y ^ 2) ^ 2 - 8 * (y + 2 / y) ^ 2 + 48 = (y - 2 / y) ^ 4 := by
    field_simp
    ring
  rw [h1]
  have h2 : Real.sqrt ((y - 2 / y) ^ 4) = (y - 2 / y) ^ 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [sq_nonneg (y - 2 / y), sq_nonneg (y ^ 2 - 4), sq_nonneg (y * y - 2 * 2), sq_nonneg (y * y - 2 / y * y), sq_nonneg (y ^ 2 - 4 / y ^ 2), sq_pos_of_ne_zero hy
  ]
  exact h2