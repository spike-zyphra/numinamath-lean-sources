import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_148775 :
  {x : ℝ | x^2 - 2 * x + 1 - abs (x^3 - 1) - 2 * (x^2 + x + 1)^2 ≥ 0} =
  {x | -1 ≤ x ∧ x ≤ -1 / 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First direction: if x^2 - 2x + 1 - abs (x^3 - 1) - 2 * (x^2 + x + 1)^2 ≥ 0, then x ∈ [-1, -1/2]
    intro h
    by_cases h1 : x ^ 3 - 1 ≥ 0
    · -- When x^3 - 1 >= 0, i.e., x >= 1, then |x^3 -1|=x^3 -1
      have h2 : abs (x ^ 3 - 1) = x ^ 3 - 1 := abs_of_nonneg h1
      rw [h2] at h
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 1)]
    · -- When x^3 -1 < 0, i.e., x < 1, then |x^3 -1|=1 -x^3
      have h1 : abs (x ^ 3 - 1) = 1 - x ^ 3 := by
        rw [abs_of_neg]
        linarith
        all_goals nlinarith
      rw [h1] at h
      constructor
      · -- Proving -1 ≤ x
        nlinarith [sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1/4), sq_nonneg (x + 1/2), sq_nonneg (x ^ 2 - x * 2), sq_nonneg (x * 2 + 1), sq_nonneg (x^3 - 1)]
      · -- Proving x ≤ -1/2
        nlinarith [sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1/4), sq_nonneg (x + 1/2), sq_nonneg (x ^ 2 - x * 2), sq_nonneg (x * 2 + 1), sq_nonneg (x^3 - 1)]
  · -- Second direction: if x ∈ [-1, -1/2], then the inequality holds
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h1 : x ^ 3 - 1 ≥ 0
    · -- When x^3 - 1 >= 0, i.e., x >= 1, then |x^3 -1|=x^3 -1
      have h2 : abs (x ^ 3 - 1) = x ^ 3 - 1 := abs_of_nonneg h1
      rw [h2]
      nlinarith [sq_nonneg (x ^ 2 - 1/4), sq_nonneg (x + 1/2), sq_nonneg (x + 1), sq_nonneg (x^2 - x * 2), sq_nonneg (x * 2 + 1), sq_nonneg (x^3 - 1)]
    · -- When x^3 -1 < 0, i.e., x < 1, then |x^3 -1|=1 -x^3
      have h1 : abs (x ^ 3 - 1) = 1 - x ^ 3 := by
        rw [abs_of_neg]
        linarith
        all_goals nlinarith
      rw [h1]
      nlinarith [sq_nonneg (x ^ 2 - 1/4), sq_nonneg (x + 1/2), sq_nonneg (x + 1), sq_nonneg (x^2 - x * 2), sq_nonneg (x * 2 + 1), sq_nonneg (x^3 - 1)]