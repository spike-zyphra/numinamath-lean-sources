import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_193826 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x * abs (3 - x) - (x - 3) * abs x) :
  IsGreatest (range f) 4.5 ∧ IsLeast (range f) 0 := by
  constructor
  · -- Show 4.5 is greatest
    constructor
    · -- Show 4.5 in range
      use (3 / 2)
      rw [h₀]
      have h1 : abs (3 - (3 / 2 : ℝ)) = 3 / 2 := by
        norm_num [abs]
      have h2 : abs ((3 / 2 : ℝ) : ℝ) = (3 / 2 : ℝ) := by
        norm_num [abs]
      rw [h1, h2]
      norm_num
    · -- Show that 4.5 is greatest
      intro y
      rintro ⟨x, hx⟩
      rw [h₀] at hx
      by_cases h1 : x ≥ 3
      · -- Case where x ≥ 3
        have h2 : abs (3 - x) = x - 3 := by
          rw [abs_of_nonpos]
          linarith
          all_goals linarith
        have h3 : abs x = x := by
          apply abs_of_nonneg
          linarith
        rw [h2, h3] at hx
        nlinarith
      by_cases h2 : x ≥ 0
      · -- Case where 0 ≤ x < 3
        have h3 : abs (3 - x) = 3 - x := by
          rw [abs_of_pos]
          linarith
        have h4 : abs x = x := by
          apply abs_of_nonneg
          linarith
        rw [h3, h4] at hx
        nlinarith [sq_nonneg (x - 1.5)]
      · -- Case where x < 0
        have h3 : abs (3 - x) = 3 - x := by
          rw [abs_of_pos]
          linarith
        have h4 : abs x = -x := by
          apply abs_of_nonpos
          linarith
        rw [h3, h4] at hx
        nlinarith
  · -- Show 0 is least
    constructor
    · -- Show 0 in range
      use (0)
      rw [h₀]
      norm_num [abs]
    · -- Show others ≥ 0
      intro y
      rintro ⟨x, hx⟩
      rw [h₀] at hx
      by_cases h1 : x ≥ 3
      · -- Case where x ≥ 3
        have h2 : abs (3 - x) = x - 3 := by
          rw [abs_of_nonpos]
          linarith
          all_goals linarith
        have h3 : abs x = x := by
          apply abs_of_nonneg
          linarith
        rw [h2, h3] at hx
        nlinarith
      by_cases h2 : x ≥ 0
      · -- Case where 0 ≤ x < 3
        have h3 : abs (3 - x) = 3 - x := by
          rw [abs_of_pos]
          linarith
        have h4 : abs x = x := by
          apply abs_of_nonneg
          linarith
        rw [h3, h4] at hx
        nlinarith [sq_nonneg (x), sq_nonneg ((3 - x) : ℝ)]
      · -- Case where x < 0
        have h3 : abs (3 - x) = 3 - x := by
          rw [abs_of_pos]
          linarith
        have h4 : abs x = -x := by
          apply abs_of_nonpos
          linarith
        rw [h3, h4] at hx
        nlinarith