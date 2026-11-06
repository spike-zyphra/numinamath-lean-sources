import Mathlib

open Real Set
open scoped BigOperators

/- Let $f(x)=\min \left\{ 2x+3,{{x}^{2}}+1,11-3x \right\}$, then the value of $\max f(x)$ is ___          ___. -/
theorem algebra_10899 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = min (min (2 * x + 3) (x ^ 2 + 1)) (11 - 3 * x)) :
  IsGreatest (range f) 5 := by
  constructor
  · -- 5 is attained by f(2)
    use 2
    norm_num [h₀]
  · -- Show that 5 is an upper bound
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    by_cases h1 : 2 * x + 3 ≤ x ^ 2 + 1
    · -- Case where 2 * x + 3 ≤ x ^ 2 + 1
      have h2 : min (2 * x + 3) (x ^ 2 + 1) = 2 * x + 3 := by
        apply min_eq_left
        linarith
      rw [h2] at hx
      by_cases h3 : 2 * x + 3 ≤ 11 - 3 * x
      · -- Case where 2 * x + 3 ≤ 11 - 3 * x
        have h4 : min (2 * x + 3) (11 - 3 * x) = 2 * x + 3 := by
          apply min_eq_left
          linarith
        rw [h4] at hx
        nlinarith
      · -- Case where 2 * x + 3 > 11 - 3 * x
        have h4 : min (2 * x + 3) (11 - 3 * x) = 11 - 3 * x := by
          apply min_eq_right
          linarith
        rw [h4] at hx
        nlinarith
    · -- Case where x ^ 2 + 1 < 2 * x + 3
      have h2 : min (2 * x + 3) (x ^ 2 + 1) = x ^ 2 + 1 := by
        apply min_eq_right
        linarith
      rw [h2] at hx
      by_cases h3 : x ^ 2 + 1 ≤ 11 - 3 * x
      · -- Case where x ^ 2 + 1 ≤ 11 - 3 * x
        have h4 : min (x ^ 2 + 1) (11 - 3 * x) = x ^ 2 + 1 := by
          apply min_eq_left
          linarith
        rw [h4] at hx
        nlinarith
      · -- Case where x ^ 2 + 1 > 11 - 3 * x
        have h4 : min (x ^ 2 + 1) (11 - 3 * x) = 11 - 3 * x := by
          apply min_eq_right
          linarith
        rw [h4] at hx
        nlinarith