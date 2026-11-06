import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303664 {f : ℝ → ℝ}
  (hf : ∀ x, f x = max (max (2 * x) (x + 3)) (-x + 3)) :
  IsLeast (range f) 3 := by
  constructor
  · -- Show that 3 is attained by f
    use 0
    norm_num [hf]
  · -- Show that 3 is indeed minimal: for any y in the range of f, y ≥ 3
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    by_cases h1 : 2 * x ≥ x + 3
    · -- Case where max (max (2*x) (x + 3)) = 2*x
      have h2 : max (2 * x) (x + 3) = 2 * x := by
        apply max_eq_left
        linarith
      rw [h2] at hx
      by_cases h3 : 2 * x ≥ -x + 3
      · -- Case where max (max (2*x) (x + 3)) (-x + 3) = 2*x
        have h4 : max (2 * x) (-x + 3) = 2 * x := by
          apply max_eq_left
          linarith
        rw [h4] at hx
        linarith
      · -- Case where max (max (2*x) (x + 3)) (-x + 3) = -x + 3
        have h4 : max (2 * x) (-x + 3) = -x + 3 := by
          apply max_eq_right
          linarith
        rw [h4] at hx
        nlinarith
    · -- Case where max (max (2*x) (x + 3)) = x + 3
      have h2 : max (2 * x) (x + 3) = x + 3 := by
        apply max_eq_right
        linarith
      rw [h2] at hx
      by_cases h3 : x + 3 ≥ -x + 3
      · -- Case where max (max (2*x) (x + 3)) (-x + 3) = x + 3
        have h4 : max (x + 3) (-x + 3) = x + 3 := by
          apply max_eq_left
          linarith
        rw [h4] at hx
        linarith
      · -- Case where max (max (2*x) (x + 3)) (-x + 3) = -x + 3
        have h4 : max (x + 3) (-x + 3) = -x + 3 := by
          apply max_eq_right
          linarith
        rw [h4] at hx
        linarith