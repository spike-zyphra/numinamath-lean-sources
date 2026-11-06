import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10433 {f : ℝ → ℝ}
  (hf : ∀ x, f x = min (min (x^2) (6 - x)) (2 * x + 15)) :
  IsGreatest (range f) 9 := by
  constructor
  · -- Show that there exists an input x such that f(x) = 9
    use -3
    norm_num [hf]
  · -- Show that no value greater than 9 is attained by f
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    have h1 : min (min (x ^ 2) (6 - x)) (2 * x + 15) ≤ 9 := by
      by_cases h2 : x^2 ≤ 6 - x
      · -- Case where x^2 ≤ 6 - x
        have h3 : min (x ^ 2) (6 - x) = x ^ 2 := by
          apply min_eq_left
          nlinarith
        rw [h3]
        by_cases h4 : x ^ 2 ≤ 2 * x + 15
        · -- Case where x^2 ≤ 2 * x + 15
          have h5 : min (x ^ 2) (2 * x + 15) = x ^ 2 := by
            apply min_eq_left
            nlinarith
          rw [h5]
          nlinarith [sq_nonneg (x + 3)]
        · -- Case where 2 * x + 15 < x^2
          have h5 : min (x ^ 2) (2 * x + 15) = 2 * x + 15 := by
            apply min_eq_right
            nlinarith
          rw [h5]
          nlinarith [sq_nonneg (x + 3)]
      · -- Case where 6 - x ≤ x^2
        have h3 : min (x ^ 2) (6 - x) = 6 - x := by
          apply min_eq_right
          nlinarith
        rw [h3]
        by_cases h4 : 6 - x ≤ 2 * x + 15
        · -- Case where 6 - x ≤ 2 * x + 15
          have h5 : min (6 - x) (2 * x + 15) = 6 - x := by
            apply min_eq_left
            linarith
          rw [h5]
          nlinarith [sq_nonneg (x + 3)]
        · -- Case where 2 * x + 15 < 6 - x
          have h5 : min (6 - x) (2 * x + 15) = 2 * x + 15 := by
            apply min_eq_right
            linarith
          rw [h5]
          nlinarith [sq_nonneg (x + 3)]
    linarith [h1, hx]