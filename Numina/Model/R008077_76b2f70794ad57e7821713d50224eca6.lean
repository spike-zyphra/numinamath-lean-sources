import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21803 (F : ℝ → ℝ) (hF : F = λ x => abs (x + 1) + abs (x - 5)) :
    range F = Ici 6 := by
  ext y
  simp only [hF, mem_range, mem_setOf_eq, mem_Ici]
  constructor
  · -- Assume y in range F, show y ≥ 6
    intro hy
    rcases hy with ⟨x, hx⟩
    by_cases h1 : x + 1 ≥ 0
    · -- If x + 1 ≥ 0, then |x + 1| = x + 1
      rw [abs_of_nonneg h1] at hx
      by_cases h2 : x - 5 ≥ 0
      · -- If x - 5 ≥ 0, then |x - 5| = x - 5
        rw [abs_of_nonneg h2] at hx
        linarith
      · -- If x - 5 < 0, then |x - 5| = -(x - 5)
        rw [abs_of_neg (lt_of_not_ge h2)] at hx
        linarith
    · -- If x + 1 < 0, then |x + 1| = -(x + 1)
      rw [abs_of_neg (lt_of_not_ge h1)] at hx
      by_cases h2 : x - 5 ≥ 0
      · -- If x - 5 ≥ 0, then |x - 5| = x - 5
        rw [abs_of_nonneg h2] at hx
        linarith
      · -- If x - 5 < 0, then |x - 5| = -(x - 5)
        rw [abs_of_neg (lt_of_not_ge h2)] at hx
        linarith
  · -- Assume y ≥ 6, show there's some x such that F(x) = y
    intro hy
    use (y + 4) / 2
    rw [abs_of_nonneg (show ((y + 4 : ℝ) / 2) + 1 ≥ 0 by linarith)]
    rw [abs_of_nonneg (show ((y + 4 : ℝ) / 2) - 5 ≥ 0 by linarith)]
    all_goals linarith