import Mathlib

open Real

theorem inequalities_3771 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x ^ 3 / (4 * x ^ 2 + (x + y) ^ 2) + y ^ 3 / (4 * y ^ 2 + (x + y) ^ 2)) ≥
    (x + y) / 8 ↔ (x ^ 2 - y ^ 2) ^ 2 ≥ 0 := by
  constructor
  · -- First rewrite the inequality as equivalent to a quadratic inequality.
    intro h
    have h1 : (x ^ 2 - y ^ 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    assumption
  · -- Now rewrite the direction from the second side.
    intro h
    have h2 : x ^ 3 / (4 * x ^ 2 + (x + y) ^ 2) + y ^ 3 / (4 * y ^ 2 + (x + y) ^ 2) ≥ (x + y) / 8 := by
      have hx1 : 0 < x := hx
      have hy1 : 0 < y := hy
      have hx2 : 0 < 4 * x ^ 2 + (x + y) ^ 2 := by
        nlinarith [hx, hy, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x + y)]
      have hy2 : 0 < 4 * y ^ 2 + (x + y) ^ 2 := by
        nlinarith [hx, hy, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x + y)]
      have h3 : (x ^ 3 / (4 * x ^ 2 + (x + y) ^ 2) + y ^ 3 / (4 * y ^ 2 + (x + y) ^ 2) ) - (x + y) / 8 ≥ 0 := by
        have h4 : (x ^ 3 / (4 * x ^ 2 + (x + y) ^ 2) + y ^ 3 / (4 * y ^ 2 + (x + y) ^ 2) ) - (x + y) / 8 =
            ( (8 * x ^ 3 * (4 * y ^ 2 + (x + y) ^ 2 ) + 8 * y ^ 3 * (4 * x ^ 2 + (x + y) ^ 2 ) - (x + y) * (4 * x ^ 2 + (x + y) ^ 2 ) * (4 * y ^ 2 + (x + y) ^ 2 )) / ( 8 * (4 * x ^ 2 + (x + y) ^ 2 ) * (4 * y ^ 2 + (x + y) ^ 2 ) ) ) := by
          field_simp
          ring
        rw [h4]
        apply div_nonneg
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x * (x - y) - y * (x - y)), sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), mul_pos hx hy, sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - y^2), sq_nonneg ((x * y)), sq_nonneg (x - y), sq_nonneg (x^2 - y^2), sq_nonneg ((x + y)), sq_nonneg (x^4 - y^4) ]
        all_goals
          positivity
      linarith [h3]
    linarith [h2]