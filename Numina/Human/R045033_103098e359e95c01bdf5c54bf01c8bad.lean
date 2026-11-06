import Mathlib

theorem inequalities_249099 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : a ^ 1997 + b ^ 1997 = a ^ 1995 + b ^ 1995) :
    a ^ 2 + b ^ 2 ≤ 2 := by
  refine le_of_mul_le_mul_left ?_ (show 0 < a ^ 1997 + b ^ 1997 by positivity)
  nth_rewrite 1 [h₁]
  suffices 0 ≤ (a ^ 2 - b ^ 2) * (a ^ 1995 - b ^ 1995) by linear_combination this
  rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos]
  repeat rw [pow_le_pow_iff_left₀ (by positivity) (by positivity) (by simp)]
  simp [le_total]
