import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_293964 (x y : ℝ) :
  abs x + abs y ≤ sqrt (2 * (x ^ 2 + y ^ 2)) ∧
  sqrt (2 * (x ^ 2 + y ^ 2)) ≤ 2 * max (abs x) (abs y) := by 
  constructor
  · -- Prove the left part of the conjunction: |x| + |y| ≤ sqrt (2 * (x ^ 2 + y ^ 2))
    have h1 : (abs x + abs y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
      have h2 : (abs x + abs y) ^ 2 = (abs x) ^ 2 + (abs y) ^ 2 + 2 * (abs x * abs y) := by
        ring
      rw [h2]
      have h3 : (abs x) ^ 2 = x ^ 2 := by
        simp [abs_pow]
      have h4 : (abs y) ^ 2 = y ^ 2 := by
        simp [abs_pow]
      rw [h3, h4]
      have h5 : (abs x - abs y) ^ 2 ≥ 0 := by
        apply sq_nonneg
      have h6 : (abs x) ^ 2 + (abs y) ^ 2 ≥ 2 * (abs x * abs y) := by
        have h7 : (abs x - abs y) ^ 2 ≥ 0 := by
          apply sq_nonneg
        nlinarith [abs_nonneg x, abs_nonneg y]
      nlinarith [abs_nonneg x, abs_nonneg y, sq_nonneg (x - y), sq_nonneg (x + y)]
    have h2 : abs x + abs y ≥ 0 := by
      linarith [abs_nonneg x, abs_nonneg y]
    have h3 : sqrt (2 * (x ^ 2 + y ^ 2)) ≥ 0 := by
      positivity
    have h4 : (abs x + abs y) ^ 2 ≤ (sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 := by
      have h5 : (sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [h1, h5, abs_nonneg x, abs_nonneg y]
    nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), abs_nonneg x, abs_nonneg y]
  · -- Prove the right part of the conjunction: sqrt (2 * (x ^ 2 + y ^ 2)) ≤ 2 * max (abs x) (abs y)
    have h1 : (sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 ≤ (2 * max (abs x) (abs y)) ^ 2 := by
      have h3 : (sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by
        rw [Real.sq_sqrt]
        positivity
      have h4 : (2 * max (abs x) (abs y)) ^ 2 = 4 * (max (abs x) (abs y) ) ^ 2 := by
        ring
      have h5 : x ^ 2 + y ^ 2 ≤ 2 * (max (abs x) (abs y) ) ^ 2 := by
        cases max_cases (abs x) (abs y) with
        | inl h =>
          have h6 : abs x ^ 2 = x ^ 2 := by
            simp [abs_pow]
          have h7 : abs y ^ 2 = y ^ 2 := by
            simp [abs_pow]
          nlinarith [abs_nonneg x, abs_nonneg y, h, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (abs x - abs y)]
        | inr h =>
          have h6 : abs x ^ 2 = x ^ 2 := by
            simp [abs_pow]
          have h7 : abs y ^ 2 = y ^ 2 := by
            simp [abs_pow]
          nlinarith [abs_nonneg x, abs_nonneg y, h, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (abs x - abs y)]
      nlinarith [h3, h4, abs_nonneg x, abs_nonneg y]
    have h5 : sqrt (2 * (x ^ 2 + y ^ 2)) ≥ 0 := by
      positivity
    have h6 : (2 * max (abs x) (abs y)) ≥ 0 := by
      positivity
    nlinarith [h1, Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), abs_nonneg x, abs_nonneg y]