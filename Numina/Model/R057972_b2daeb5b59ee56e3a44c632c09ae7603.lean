import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_318870 :
  {a : ℝ | ∀ x : ℝ, abs (2 * x - a) + abs (3 * x - 2 * a) ≥ a ^ 2} =
  {a | -1 / 3 ≤ a ∧ a ≤ 1 / 3} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · -- First direction: if a satisfies the inequality for all x, then -1/3 ≤ a ≤ 1/3
      intro h
      have h1 := h (2 * a / 3)
      have h2 : abs (2 * (2 * a / 3) - a) + abs (3 * (2 * a / 3) - 2 * a) ≥ a ^ 2 := h1
      have eq1 : abs (2 * (2 * a / 3) - a) = abs (a / 3) := by
        ring_nf
        <;> linarith
      have eq2 : abs (3 * (2 * a / 3) - 2 * a) = 0 := by 
        ring_nf
        <;> simp
      rw [eq1, eq2] at h2 
      by_cases ha : a ≥ 0
      · -- If a ≥ 0, then |a/3| = a/3
        rw [abs_of_nonneg (by nlinarith)] at h2
        constructor
        · -- Show -1/3 ≤ a
          linarith
        · -- Show a ≤ 1/3
          nlinarith [h2]
      · -- a < 0
        rw [abs_of_neg (by nlinarith)] at h2
        constructor
        · -- Show -1/3 ≤ a
          nlinarith [h2]
        · -- Show a ≤ 1/3
          nlinarith [h2]
    · -- Second direction: if -1/3 ≤ a ≤ 1/3, then a satisfies the inequality for all x
      rintro ⟨h1, h2⟩
      intro x
      have h3 : abs (2 * x - a) + abs (3 * x - 2 * a) ≥ a ^ 2 := by
        by_cases h11 : 2 * x - a ≥ 0
        · -- If 2x - a ≥ 0
          by_cases h12 : 3 * x - 2 * a ≥ 0
          · -- If 3x - 2a ≥ 0
            rw [abs_of_nonneg h11, abs_of_nonneg h12]
            nlinarith [sq_nonneg (x - 2 * a / 5), sq_nonneg (a), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
          · -- If 3x - 2a < 0
            rw [abs_of_nonneg h11, abs_of_neg (lt_of_not_ge h12)]
            nlinarith [sq_nonneg (x - a / 1), sq_nonneg (a), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
        · -- If 2x - a < 0
          by_cases h12 : 3 * x - 2 * a ≥ 0
          · -- If 3x - 2a ≥ 0
            rw [abs_of_neg (lt_of_not_ge h11), abs_of_nonneg h12]
            nlinarith [sq_nonneg (x - a / 1), sq_nonneg (a), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
          · -- If 3x - 2a < 0
            rw [abs_of_neg (lt_of_not_ge h11), abs_of_neg (lt_of_not_ge h12)]
            nlinarith [sq_nonneg (x - a / 3 / 1), sq_nonneg (a), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
      linarith [h3]