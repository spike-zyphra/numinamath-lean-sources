import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_317986 (x y a : ℝ) (h₀ : x^2 + y^2 = a^2) (h₁ : a^2 < 1) :
    1 + sqrt (1 - a^2) ≤ sqrt (1 - x^2) + sqrt (1 - y^2) ∧
    sqrt (1 - x^2) + sqrt (1 - y^2) ≤ sqrt (4 - 2 * a^2) := by

  constructor

  · -- Prove the minimum bound: 1 + sqrt(1 - a^2) ≤ sqrt(1 - x^2) + sqrt(1 - y^2)
    have h2 : x^2 ≤ 1 := by
      nlinarith [sq_nonneg y, sq_nonneg a, h₀, h₁]
    have h3 : y^2 ≤ 1 := by
      nlinarith [sq_nonneg x, sq_nonneg a, h₀, h₁]

    have h4 : 1 - x^2 ≥ 0 := by nlinarith
    have h5 : 1 - y^2 ≥ 0 := by nlinarith

    have h6 : (sqrt (1 - x^2) + sqrt (1 - y^2)) ^ 2 ≥ (1 + sqrt (1 - a^2)) ^ 2 := by
      have h7 : (sqrt (1 - x^2) + sqrt (1 - y^2)) ^ 2 =
          (sqrt (1 - x^2)) ^ 2 + (sqrt (1 - y^2)) ^ 2 + 2 * (sqrt (1 - x^2) * sqrt (1 - y^2)) := by ring
      rw [h7]

      have h8 : (sqrt (1 - x^2)) ^ 2 = 1 - x^2 := Real.sq_sqrt (by linarith)
      have h9 : (sqrt (1 - y^2)) ^ 2 = 1 - y^2 := Real.sq_sqrt (by linarith)
      have h10 : sqrt (1 - x^2) * sqrt (1 - y^2) = sqrt ((1 - x^2) * (1 - y^2)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      rw [h8, h9, h10]

      have h11 : (1 + sqrt (1 - a^2)) ^ 2 = 1 + (sqrt (1 - a^2)) ^ 2 + 2 * (sqrt (1 - a^2)) := by
        ring_nf
      rw [h11]

      have h12 : (sqrt (1 - a^2)) ^ 2 = 1 - a^2 := Real.sq_sqrt (by nlinarith)
      rw [h12]

      have h13 : (1 - x^2) * (1 - y^2) ≥ 1 - a^2 := by
        nlinarith [sq_nonneg (x * y), sq_nonneg (x^2 + y^2 - a^2), h₀]

      have h14 : sqrt ((1 - x^2) * (1 - y^2)) ≥ sqrt (1 - a^2) := Real.sqrt_le_sqrt (by
        nlinarith [sq_nonneg (x * y), sq_nonneg (x^2 + y^2 - a^2), h₀]
      )
      nlinarith [h13, h14, Real.sqrt_nonneg ((1 - x^2) * (1 - y^2)), Real.sqrt_nonneg (1 - a^2)]

    have h15 : sqrt (1 - x^2) + sqrt (1 - y^2) ≥ 1 + sqrt (1 - a^2) := by
      nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sqrt_nonneg (1 - y^2), Real.sqrt_nonneg (1 - a^2), h6]
    linarith

  · -- Prove the maximum bound: sqrt(1 - x^2) + sqrt(1 - y^2) ≤ sqrt (4 - 2 * a^2)
    have h2 : x^2 ≤ 1 := by
      nlinarith [sq_nonneg y, sq_nonneg a, h₀, h₁]
    have h3 : y^2 ≤ 1 := by
      nlinarith [sq_nonneg x, sq_nonneg a, h₀, h₁]

    have h4 : 1 - x^2 ≥ 0 := by nlinarith
    have h5 : 1 - y^2 ≥ 0 := by nlinarith

    have h7 : (sqrt (1 - x^2) + sqrt (1 - y^2)) ^ 2 ≤ 4 - 2 * a^2 := by
      have h8 : (sqrt (1 - x^2) + sqrt (1 - y^2)) ^ 2 = (sqrt (1 - x^2)) ^ 2 + (sqrt (1 - y^2)) ^ 2 + 2 * (sqrt (1 - x^2) * sqrt (1 - y^2)) := by ring
      rw [h8]

      have h9 : (sqrt (1 - x^2)) ^ 2 = 1 - x^2 := Real.sq_sqrt (by linarith)
      have h10 : (sqrt (1 - y^2)) ^ 2 = 1 - y^2 := Real.sq_sqrt (by linarith)
      have h11 : sqrt (1 - x^2) * sqrt (1 - y^2) = sqrt ((1 - x^2) * (1 - y^2)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      rw [h9, h10, h11]

      nlinarith [Real.sq_sqrt (show 0 ≤ 1 - x^2 by linarith), Real.sq_sqrt (show 0 ≤ 1 - y^2 by linarith),
        sq_nonneg (sqrt (1 - x^2) - sqrt (1 - y^2)), sq_nonneg (x + y), sq_nonneg (x - y), Real.sq_sqrt (show 0 ≤ 1 - a^2 by nlinarith), h₀]

    have h8 : sqrt (1 - x^2) + sqrt (1 - y^2) ≤ sqrt (4 - 2 * a^2) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith