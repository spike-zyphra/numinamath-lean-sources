import Mathlib

theorem algebra_71655 (x a : ℝ) (hx : x ≠ 1) :
    ∑ i ∈ Finset.range 9, (x^(i + 1) + (i + 1)*a) =
    (x^10 - x)/(x - 1) + 45*a := by
  norm_num [Finset.sum_range_succ]
  field_simp [(show x - 1 ≠ 0 by intro h; apply hx; linarith)]
  ring