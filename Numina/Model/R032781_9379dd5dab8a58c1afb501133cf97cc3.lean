import Mathlib

theorem algebra_319505 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : |m| < |n|) (x : ℝ) (h : |x + m| + |x - n| = m + n) :
    -m ≤ x ∧ x ≤ n := by
  by_cases h1 : x ≥ n
  · -- Case 1: x ≥ n
    by_cases h2 : x + m ≥ 0
    · -- Case 1a: x + m ≥ 0 and x ≥ n
      rw [abs_of_nonneg h2, abs_of_nonneg (show x - n ≥ 0 by linarith)] at h
      constructor
      · linarith
      · linarith
    · -- Case 1b: x + m < 0 and x ≥ n
      rw [abs_of_neg (show x + m < 0 by linarith), abs_of_nonneg (show x - n ≥ 0 by linarith)] at h
      cases' abs_cases m with h11 h11 <;> cases' abs_cases n with h12 h12 <;> linarith
  · -- Case 2: x < n
    by_cases h2 : x ≥ -m
    · -- Case 2: -m ≤ x < n
      by_cases h3 : x - n ≥ 0
      · -- Case 2a: -m ≤ x and x - n ≥ 0
        exfalso
        linarith
      · -- Case 2b: -m ≤ x and x - n < 0
        rw [abs_of_nonneg (show x + m ≥ 0 by linarith), abs_of_neg (show x - n < 0 by linarith)] at h
        constructor
        · linarith
        · linarith
    · -- Case 3: x < -m
      by_cases h3 : x - n ≥ 0
      · -- Case 3a: x < -m and x - n ≥ 0
        rw [abs_of_neg (show x + m < 0 by linarith), abs_of_nonneg (show x - n ≥ 0 by linarith)] at h
        cases' abs_cases m with h11 h11 <;> cases' abs_cases n with h12 h12 <;> linarith
      · -- Case 3b: x < -m and x - n < 0
        rw [abs_of_neg (show x + m < 0 by linarith), abs_of_neg (show x - n < 0 by linarith)] at h
        cases' abs_cases m with h11 h11 <;> cases' abs_cases n with h12 h12 <;> linarith