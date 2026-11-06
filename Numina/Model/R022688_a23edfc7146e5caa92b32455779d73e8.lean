import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_235519 {f : ℝ → ℝ}
  (hf : ∀ x, f x = min (-x + 6) (-2 * x ^ 2 + 4 * x + 6)) :
  IsGreatest (range f) 6 := by
  constructor
  · -- Show 6 is attained by f, for x = 0
    use 0
    rw [hf 0]
    norm_num
  · -- Show no value greater than 6 is attained by f
    intro y
    rintro ⟨x, hx⟩
    rw [hf x] at hx
    by_cases h : (-x + 6) ≤ (-2 * x ^ 2 + 4 * x + 6)
    · -- If -x + 6 ≤ -2 * x ^ 2 + 4 * x + 6, then f(x) = -x + 6
      rw [min_eq_left h] at hx
      nlinarith [sq_nonneg (x)]
    · -- If -x + 6 > -2 * x ^ 2 + 4 * x + 6, then f(x) = -2 * x ^ 2 + 4 * x + 6
      rw [min_eq_right (le_of_not_ge h)] at hx
      nlinarith [sq_nonneg (x - 2)]