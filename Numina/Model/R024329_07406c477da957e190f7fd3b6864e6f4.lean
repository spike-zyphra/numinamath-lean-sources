import Mathlib

theorem inequalities_603287 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 4) :
    1 / x + 4 / y ≥ 9 / 4 := by
  have h1 : y = 4 - x := by linarith
  rw [h1]
  have hx1 : 0 < x := hx
  have h2 : x < 4 := by
    nlinarith
  have h3 : 0 < (4 - x) := by
    nlinarith
  have h5 : 1 / x + 4 / (4 - x) - 9 / 4 ≥ 0 := by
    have h6 : 0 < x * (4 - x) := by
      positivity
    have h7 : (1 / x + 4 / (4 - x) - 9 / 4) = ((4 - x) + 4 * x - (9 / 4) * (x * (4 - x)) ) / (x * (4 - x) ) := by
      field_simp
      ring
    have h8 : (4 - x) + 4 * x - (9 / 4) * (x * (4 - x)) ≥ 0 := by
      nlinarith [sq_nonneg (x - 4 / 3), sq_nonneg ((4 - x) - 4 / 3), sq_nonneg (x - (4 - x)), sq_nonneg (x - 2), sq_nonneg ((4 - x) - 2), mul_pos hx1 (show 0 < (4 - x) by nlinarith) ]
    rw [h7] at *
    apply div_nonneg
    linarith
    all_goals nlinarith
  linarith