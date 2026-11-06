import Mathlib

theorem algebra_12333 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : ((x + 2)^2 / y + (y + 2)^2 / x = 16)) : x + y = 4 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have eq1 : (x + 2) ^ 2 * x + (y + 2) ^ 2 * y = 16 * (x * y) := by
    have eq3 : ((x + 2) ^ 2 / y + (y + 2) ^ 2 / x = 16) := h
    have eq4 : (x + 2) ^ 2 * x + (y + 2) ^ 2 * y = 16 * (x * y) := by
      field_simp [show 0 < y by linarith, show 0 < x by linarith] at eq3 ⊢
      nlinarith [mul_pos hx hy]
    linarith
  have h3 : (x + y - 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x - 2), sq_nonneg (y - 2),
      mul_pos hx hy
    ]
  have h4 : x + y - 4 = 0 := by
    apply pow_eq_zero 
    exact h3
  linarith