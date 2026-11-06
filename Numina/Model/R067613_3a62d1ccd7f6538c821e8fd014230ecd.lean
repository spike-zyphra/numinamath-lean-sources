import Mathlib

theorem inequalities_320175 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : p^3 + q^3 = 2) : p + q ≤ 2 := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + q - 2), sq_nonneg (p^2 + q^2 - 1),
          sq_nonneg (p^3 + q^3 - 2), sq_nonneg (p^2 + q^2 - (p + q)), mul_pos hp hq,
          sq_nonneg (p - 1), sq_nonneg (q - 1)]