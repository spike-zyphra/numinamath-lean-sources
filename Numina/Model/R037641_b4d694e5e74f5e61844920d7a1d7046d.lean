import Mathlib

open Real Set

theorem inequalities_12766 :
    (∀ x y : ℝ, |x| < 1 ∧ |y| < 1 ↔ |x + y| + |x - y| < 2) := by
  intro x y
  constructor
  · -- Assume |x| < 1 and |y| < 1, prove |x+y| + |x-y| < 2
    rintro ⟨hx, hy⟩
    have h1 : -1 < x := by linarith [abs_lt.mp hx]
    have h2 : x < 1 := by linarith [abs_lt.mp hx]
    have h3 : -1 < y := by linarith [abs_lt.mp hy]
    have h4 : y < 1 := by linarith [abs_lt.mp hy]
    by_cases h5 : x + y ≥ 0
    · -- If x + y ≥ 0, need to check the sign of x - y
      by_cases h6 : x - y ≥ 0
      · -- If x - y ≥ 0
        rw [abs_of_nonneg h5, abs_of_nonneg h6]
        linarith
      · -- If x - y < 0
        rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)]
        linarith
    · -- If x + y < 0
      by_cases h7 : x - y ≥ 0
      · -- If x - y ≥ 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7]
        linarith
      · -- If x - y < 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)]
        linarith
  · -- Assume |x+y| + |x-y| < 2, prove |x| < 1 and |y| < 1
    intro h
    by_cases h5 : x + y ≥ 0
    · -- If x + y ≥ 0, need to check the sign of x - y
      by_cases h6 : x - y ≥ 0
      · -- If x - y ≥ 0
        rw [abs_of_nonneg h5, abs_of_nonneg h6] at h
        constructor
        · -- Show |x| < 1
          rw [abs_lt]
          constructor <;> linarith
        · -- Show |y| < 1
          rw [abs_lt]
          constructor <;> linarith
      · -- If x - y < 0
        rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)] at h
        constructor
        · -- Show |x| < 1
          rw [abs_lt]
          constructor <;> linarith
        · -- Show |y| < 1
          rw [abs_lt]
          constructor <;> linarith
    · -- If x + y < 0
      by_cases h7 : x - y ≥ 0
      · -- If x - y ≥ 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7] at h
        constructor
        · -- Show |x| < 1
          rw [abs_lt]
          constructor <;> linarith
        · -- Show |y| < 1
          rw [abs_lt]
          constructor <;> linarith
      · -- If x - y < 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h
        constructor
        · -- Show |x| < 1
          rw [abs_lt]
          constructor <;> linarith
        · -- Show |y| < 1
          rw [abs_lt]
          constructor <;> linarith