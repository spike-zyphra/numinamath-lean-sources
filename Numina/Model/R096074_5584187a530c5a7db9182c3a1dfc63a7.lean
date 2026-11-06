import Mathlib

open Real

theorem inequalities_292898 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + 2 / y) * (y / x + 2) ≥ 8 := by
  have h2 : (x + 2 / y) * (y / x + 2) = y + 2 * x + 2 / x + 4 / y := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    <;> ring_nf
    <;> field_simp [ne_of_gt hx, ne_of_gt hy]
    <;> ring
  rw [h2] at *
  have h7 : y + 4 / y ≥ 4 := by
    have h8 : y * (4 / y) = 4 := by
      field_simp [ne_of_gt hy]
      <;> nlinarith
    nlinarith [sq_nonneg (y - 2), mul_pos hx hy]
  have h8 : 2 * x + 2 / x ≥ 4 := by
    have h9 : (2 * x + 2 / x) - 4 ≥ 0 := by
      have h9 : (2 * x + 2 / x - 4) = (2 * x ^ 2 + 2 - 4 * x) / x := by
        field_simp
        <;> ring
      rw [h9]
      apply div_nonneg
      nlinarith [sq_nonneg (x - 1)]
      linarith [show 0 < x from by linarith]
    linarith
  linarith [h7, h8, mul_pos hx hy]