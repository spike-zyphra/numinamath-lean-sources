import Mathlib

theorem algebra_7972 {y : ℝ → ℝ} (hy : ∀ x, y x = x + abs (x - 1)) :
    IsLeast (Set.range y) 1 := by
  constructor
  · -- First, we need to show that 1 is in the range of y
    use 1
    norm_num [hy]
  · -- Now, we need to show that for all y(x), y(x) ≥ 1
    intro y_val
    rintro ⟨x, hx⟩
    rw [hy] at hx
    by_cases h : x - 1 ≥ 0
    · -- Case where x ≥ 1, so |x - 1| = x - 1
      rw [abs_of_nonneg h] at hx
      linarith
    · -- Case where x < 1, so |x - 1| = 1 - x
      rw [abs_of_neg (lt_of_not_ge h)] at hx
      linarith