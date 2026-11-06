import Mathlib

theorem algebra_90757 {x1 x2 : ℝ} (hx1 : x1^2 + 5 * x1 - 7 = 0) (hx2 : x2^2 + 5 * x2 - 7 = 0)
    (hxy : x1 ≠ x2) :
    x1^3 + 5 * x1^2 - 4 * x1 + x1^2 * x2 - 4 * x2 = 20 := by
  have eq1 : x1^2 = -5 * x1 + 7 := by linarith
  have eq2 : x2^2 = -5 * x2 + 7 := by linarith
  have hsum : x1 + x2 = -5 := by
    have h1 : (x1 - x2) * (x1 + x2 + 5) = 0 := by
      linarith [eq1, eq2]
    rcases (mul_eq_zero.mp h1) with (h1 | h2)
    . exfalso
      exact hxy (by linarith)
    . linarith
  have hprod : x1 * x2 = -7 := by
    rw [pow_two] at hx1
    nth_rw 1 [show x1 = -5 - x2 by linarith] at hx1
    ring_nf at hx1
    linarith only [hx1]
  calc
    _ = x1 * (x1 ^ 2 + 5 * x1 - 4) + x2 * (x1 ^ 2 - 4) := by ring
    _ = x1 * (-5 * x1 + 7 + 5 * x1 - 4) + x2 * (-5 * x1 + 7 - 4) := by rw [eq1]
    _ = 3 * (x1 + x2) - 5 * (x1 * x2) := by ring
    _ = 3 * -5 - 5 * -7 := by rw [hsum, hprod]
    _ = 20 := by norm_num