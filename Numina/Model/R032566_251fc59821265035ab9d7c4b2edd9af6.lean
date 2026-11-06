import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12717 (f : ℝ → ℝ) (hf : f = λ x => abs (x + 1) - abs (x - 1)) :
    range f = Icc (-2) 2 := by
  ext y
  simp [hf]
  constructor
  · -- Show that if y is in the range of f, then y in Icc (-2) (2)
    intro hy
    rcases hy with ⟨x, hx⟩
    by_cases h1 : x < -1
    · -- Case 1: x < -1
      rw [abs_of_neg (show x + 1 < 0 by linarith), abs_of_neg (show x - 1 < 0 by linarith)] at hx
      constructor <;> linarith
    · -- Now x ≥ -1
      by_cases h2 : x ≤ 1
      · -- Case 2: -1 ≤ x ≤ 1
        rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at hx
        constructor <;> linarith
      · -- Case 3: x > 1
        rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonneg (show x - 1 ≥ 0 by linarith)] at hx
        constructor <;> linarith
  · -- Show that any y in Icc (-2) (2) is in the range of f
    rintro ⟨hy1, hy2⟩
    use (y / 2)
    have h3 : (y / 2 : ℝ) + 1 ≥ 0 := by
      linarith
    have h4 : (y / 2 : ℝ) - 1 ≤ 0 := by
      linarith
    rw [abs_of_nonneg (show (y / 2 : ℝ) + 1 ≥ 0 by linarith), abs_of_nonpos (show (y / 2 : ℝ) - 1 ≤ 0 by linarith)]
    all_goals
      ring_nf <;> linarith