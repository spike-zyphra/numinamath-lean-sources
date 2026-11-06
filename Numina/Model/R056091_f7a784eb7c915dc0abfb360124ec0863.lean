import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_237119 (f : ℝ → ℝ) (hf : f = λ x => min (2 - x^2) x) :
    IsGreatest (range f) 1 := by 
  constructor
  · -- Show that 1 belongs to the range of f
    use 1
    simp [hf]
    norm_num
  · -- Show that no value greater than 1 is in the range of f 
    intro y
    rintro ⟨x, hx⟩
    simp [hf] at hx
    by_contra h
    push_neg at h
    by_cases h1 : (2 - x ^ 2) ≤ x
    · -- Case where 2 - x^2 ≤ x, so min (2 - x ^ 2) x = 2 - x ^ 2
      have h2 : min (2 - x ^ 2) x = 2 - x ^ 2 := by
        rw [min_eq_left]
        all_goals linarith
      rw [h2] at hx
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2)]
    · -- Case where 2 - x^2 > x, so min (2 - x ^ 2) x = x
      have h2 : min (2 - x ^ 2) x = x := by
        rw [min_eq_right]
        all_goals linarith
      rw [h2] at hx
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2)]