import Mathlib

theorem inequalities_319914 (x y : ℝ) :
    (|x| < 1 ∧ |y| < 1) ↔ (|x + y| + |x - y| < 2) := by
  constructor
  · -- Assume |x| < 1 ∧ |y| < 1, prove |x + y| + |x - y| < 2
    intro h
    rcases h with ⟨hx, hy⟩
    have h1 : -1 < x := by linarith [abs_lt.mp hx]
    have h2 : x < 1 := by linarith [abs_lt.mp hx]
    have h3 : -1 < y := by linarith [abs_lt.mp hy]
    have h4 : y < 1 := by linarith [abs_lt.mp hy]
    by_cases h5 : x + y ≥ 0
    · -- x + y ≥ 0
      by_cases h6 : x - y ≥ 0
      · -- x - y ≥ 0
        rw [abs_of_nonneg h5, abs_of_nonneg h6]
        linarith
      · -- x - y < 0
        rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)]
        linarith
    · -- x + y < 0
      by_cases h7 : x - y ≥ 0
      · -- x - y ≥ 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7]
        linarith
      · -- x - y < 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)]
        linarith
  · -- Assume |x + y| + |x - y| < 2, prove |x| < 1 ∧ |y| < 1
    intro h
    constructor
    · -- Prove |x| < 1
      by_cases h1 : x ≥ 0
      · -- x ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h5 : x + y ≥ 0
        · -- x + y ≥ 0
          by_cases h6 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_nonneg h5, abs_of_nonneg h6] at h
            linarith
          · -- x - y < 0
            rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
        · -- x + y < 0
          by_cases h7 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7] at h
            linarith
          · -- x - y < 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
      · -- x < 0
        rw [abs_of_neg (show x < 0 by linarith)]
        by_cases h5 : x + y ≥ 0
        · -- x + y ≥ 0
          by_cases h6 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_nonneg h5, abs_of_nonneg h6] at h
            linarith
          · -- x - y < 0
            rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
        · -- x + y < 0
          by_cases h7 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7] at h
            linarith
          · -- x - y < 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
    · -- Prove |y| < 1
      by_cases h1 : y ≥ 0
      · -- y ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h5 : x + y ≥ 0
        · -- x + y ≥ 0
          by_cases h6 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_nonneg h5, abs_of_nonneg h6] at h
            linarith
          · -- x - y < 0
            rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
        · -- x + y < 0
          by_cases h7 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7] at h
            linarith
          · -- x - y < 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
      · -- y < 0
        rw [abs_of_neg (show y < 0 by linarith)]
        by_cases h5 : x + y ≥ 0
        · -- x + y ≥ 0
          by_cases h6 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_nonneg h5, abs_of_nonneg h6] at h
            linarith
          · -- x - y < 0
            rw [abs_of_nonneg h5, abs_of_neg (show x - y < 0 by linarith)] at h
            linarith
        · -- x + y < 0
          by_cases h7 : x - y ≥ 0
          · -- x - y ≥ 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h7] at h
            linarith
          · -- x - y < 0
            rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h
            linarith