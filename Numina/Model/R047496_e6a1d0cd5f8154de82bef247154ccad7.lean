import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_97113 :
  ∀ x y : ℝ, abs x + abs y ≤ sqrt (2 * (x ^ 2 + y ^ 2)) ∧
  sqrt (2 * (x ^ 2 + y ^ 2)) ≤ 2 * max (abs x) (abs y) := by
  intro x y
  have h1 : abs x + abs y ≤ sqrt (2 * (x ^ 2 + y ^ 2)) := by
    have h11 : (abs x + abs y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by 
      have h2 : (abs x + abs y) ^ 2 = (abs x) ^ 2 + (abs y) ^ 2 + 2 * (abs x * abs y) := by ring
      have h3 : (abs x) ^ 2 = x^2 := by rw [sq_abs]
      have h4 : (abs y) ^ 2 = y^2 := by rw [sq_abs]
      rw [h2, h3, h4]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (abs x - abs y), sq_nonneg (x * y), abs_nonneg x, abs_nonneg y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]
    have h5 : abs x + abs y ≤ sqrt (2 * (x ^ 2 + y ^ 2)) := by
      have h6 : (abs x + abs y) ^ 2 ≤ (2 * (x ^ 2 + y ^ 2)) := by linarith [h11]
      have h7 : abs x + abs y ≥ 0 := by positivity
      have h8 : sqrt (2 * (x ^ 2 + y ^ 2)) ≥ 0 := by positivity
      have h9 : (abs x + abs y) ^ 2 ≤ (2 * (x ^ 2 + y ^ 2)) := by linarith [h11]
      have h10 : abs x + abs y ≤ sqrt (2 * (x ^ 2 + y ^ 2)) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (x ^ 2 + y ^ 2) by positivity : (0 : ℝ) ≤ 2 * (x ^ 2 + y ^ 2)), Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2))]
      exact h10
    exact h5
  have h7 : sqrt (2 * (x ^ 2 + y ^ 2)) ≤ 2 * max (abs x) (abs y) := by
    have h9 : 2 * (x^2 + y^2) ≤ (2 * max (abs x) (abs y)) ^ 2 := by
      by_cases h : abs x ≥ abs y
      · -- Case where abs x ≥ abs y, so max (abs x) (abs y) = abs x
        have hmax1 : max (abs x) (abs y) = abs x := by 
          apply max_eq_left h
        rw [hmax1]
        have h11 : (abs x) ^ 2 = x^2 := by rw [sq_abs]
        have h12 : (abs y) ^ 2 = y^2 := by rw [sq_abs]
        nlinarith [sq_nonneg (abs x - abs y), sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg ((abs x)^2 - (abs y)^2), mul_nonneg (abs_nonneg x) (abs_nonneg y), h, abs_nonneg x, abs_nonneg y, sq_nonneg (abs x ^ 2 - abs y ^ 2), abs_nonneg y]
      · -- Case where abs x < abs y, so max (abs x) (abs y) = abs y
        have hmax2 : max (abs x) (abs y) = abs y := by 
          apply max_eq_right (by linarith)
        rw [hmax2]
        have h13 : (abs x) ^ 2 = x^2 := by rw [sq_abs]
        have h14 : (abs y) ^ 2 = y^2 := by rw [sq_abs]
        nlinarith [sq_nonneg (abs x - abs y), sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg ((abs x)^2 - (abs y)^2), mul_nonneg (abs_nonneg x) (abs_nonneg y), h, abs_nonneg x, abs_nonneg y, sq_nonneg (abs x ^ 2 - abs y ^ 2), abs_nonneg y]
    have h15 : sqrt (2 * (x ^ 2 + y ^ 2)) ≤ (2 * max (abs x) (abs y)) := by
      have h10 : (sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 ≤ (2 * max (abs x) (abs y)) ^ 2 := by
        have h11 : (sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 = (2 * (x ^ 2 + y ^ 2)) := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [h11, h9, Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), sq_nonneg (2 * max (abs x) (abs y) - sqrt (2 * (x ^ 2 + y ^ 2)))]
      have h11 : sqrt (2 * (x ^ 2 + y ^ 2)) ≥ 0 := by positivity
      have h12 : (2 * max (abs x) (abs y)) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), sq_nonneg (2 * max (abs x) (abs y) - sqrt (2 * (x ^ 2 + y ^ 2)))]
    linarith [h15]
  constructor
  · exact h1
  · exact h7