import Mathlib

theorem inequalities_200521 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^3 ≥ x^3 + y^4) : x^3 + y^3 ≤ 2 := by
  -- prove this `x + y ^ 2 ≥ x ^ 2 + y ^ 3` by find contradiction.
  have ineq_aux : x + y ^ 2 ≥ x ^ 2 + y ^ 3 := by 
    by_contra h'
    simp at h'
    have hc : 2 * x ^ 2 + 2 *  y ^ 3 > (x +x ^ 3) + (y ^ 4 + y) := by 
      calc
        _ = (x ^ 2 + y ^ 3) + (x ^ 2 + y ^ 3) := by ring
        _ ≥ (x ^ 3 + y ^ 4) + (x ^ 2 + y ^ 3):= by linarith [h, h']
        _ > (x +x ^ 3) + (y ^ 4 + y) := by nlinarith [pow_two_nonneg (x - 1), pow_two_nonneg (y - 1), hx, hy]
    have hc1 : (x +x ^ 3) ≥ 2 * x ^ 2 := by nlinarith [pow_two_nonneg (x - 1)]
    have hc2 : (y ^ 4 + y) ≥ 2 *  y ^ 3:= by nlinarith [pow_two_nonneg (y - 1)]
    linarith
  -- then prove that `1 + x ^ 2 + 1 + y ^ 4 ≥ x ^ 2 + y ^ 3 + x ^ 3 + y ^ 4`, then use nlinarith, we can get the desire result.
  have ineq_aux1 : x + y ^ 2 ≥ x ^ 3 + y ^ 4 := by linarith
  have ineq_aux2 : 2 * x + 2 * y ^ 2 ≥  x ^ 2 + y ^ 3 + x ^ 3 + y ^ 4 := by linarith
  have ineq_aux3 : 1 + x ^ 2 ≥ 2 * x := by nlinarith [pow_two_nonneg (x - 1)]
  have ineq_aux4 : 1 + y ^ 4 ≥ 2 * y^2 := by nlinarith [pow_two_nonneg (y - 1)]
  have ineq_aux5 : 1 + x ^ 2 + 1 + y ^ 4 ≥ 2 * x + 2 * y ^ 2 := by linarith
  have ineq_aux6 : 1 + x ^ 2 + 1 + y ^ 4 ≥ x ^ 2 + y ^ 3 + x ^ 3 + y ^ 4 := by linarith
  nlinarith
  