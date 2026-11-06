import Mathlib

/- The cube root of the real number -8 is-/
theorem algebra_9121 (x : ℝ) : x ^ 3 = -8 ↔ x = -2 := by
  constructor
  swap
  -- Verify that (-2)^3=-8.
  . rintro ⟨rfl⟩
    norm_num
  -- Solve x^3=-8 using the fact that f(x)=x^3 is injective.
  intro h
  have : 0 ≤ -x := by
    by_contra hx
    push_neg at hx
    have : 0 < x := by linarith
    have : 0 < x ^ 3 := by positivity
    norm_num [h] at this
  have : (-x) ^ 3 = -x^3 := by ring
  rw [h, neg_neg, show (8 : ℝ) = 2 ^ 3 by norm_num, ← Real.rpow_natCast, ← Real.rpow_natCast,
    Real.rpow_left_inj (by assumption) (by norm_num) (by norm_num)] at this
  linear_combination -this
