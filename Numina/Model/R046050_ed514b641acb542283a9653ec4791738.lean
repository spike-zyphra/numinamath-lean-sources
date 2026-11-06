import Mathlib

theorem inequalities_51732 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    x / (x ^ 2 + y ^ 3) + y / (x ^ 3 + y ^ 2) ≤
    2 * (x / (x + y ^ 2) + y / (x ^ 2 + y)) := by
  have h1 : y = 1 - x := by linarith
  have h2 : 0 < y := by linarith
  have h3 : x / (x ^ 2 + y ^ 3) + y / (x ^ 3 + y ^ 2) - 2 * (x / (x + y ^ 2) + y / (x ^ 2 + y)) ≤ 0 := by
    have eq1 : x / (x ^ 2 + y ^ 3) + y / (x ^ 3 + y ^ 2) - 2 * (x / (x + y ^ 2) + y / (x ^ 2 + y)) =
        (x * (x ^ 3 + y ^ 2) * (x + y ^ 2) * (x ^ 2 + y) + y * (x ^ 2 + y ^ 3) * (x + y ^ 2) * (x ^ 2 + y) 
         - 2 * x * (x ^ 2 + y ^ 3) * (x ^ 3 + y ^ 2) * (x ^ 2 + y) 
         - 2 * y * (x ^ 2 + y ^ 3) * (x + y ^ 2) * (x ^ 3 + y ^ 2) ) / 
        ((x ^ 2 + y ^ 3) * (x ^ 3 + y ^ 2) * (x + y ^ 2) * (x ^ 2 + y)) := by
      field_simp
      ring
    rw [eq1]
    have h35 : 0 < (x ^ 2 + y ^ 3) * (x ^ 3 + y ^ 2) * (x + y ^ 2) * (x ^ 2 + y) := by
      positivity
    have h7 : x * (x ^ 3 + y ^ 2) * (x + y ^ 2) * (x ^ 2 + y) + y * (x ^ 2 + y ^ 3) * (x + y ^ 2) * (x ^ 2 + y) 
        - 2 * x * (x ^ 2 + y ^ 3) * (x ^ 3 + y ^ 2) * (x ^ 2 + y) 
        - 2 * y * (x ^ 2 + y ^ 3) * (x + y ^ 2) * (x ^ 3 + y ^ 2) ≤ 0 := by
      -- Substitute y = 1 - x as before.
      rw [show y = 1 - x by linarith [hxy]]
      nlinarith [sq_nonneg (x - (1 - x)), sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2), 
                  mul_pos hx (show 0 < 1 - x by nlinarith [show x < 1 by nlinarith [hxy, hx, hy]]),
                  sq_nonneg (x ^ 2 - (1 - x) ^ 2), sq_nonneg (x ^ 3 - (1 - x) ^ 3), 
                  sq_nonneg (x * (1 - x) - 1 / 4), sq_nonneg (x - (1 - x)), 
                  mul_pos hx (show 0 < (1 - x) by nlinarith [show x < 1 by nlinarith [hxy, hx, hy]])]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    all_goals positivity
  linarith