import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_152210 (n : ℕ) (hn : 0 < n) (t : ℝ)
  (h1 : ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x^(2*n) + y^(2*n) = 1000 ∧ x^n + y^n = t) :
  10 * sqrt 10 < t ∧ t ≤ 20 * sqrt 5 := by 
  rcases h1 with ⟨x, y, hx, hy, heq1, heq2⟩
  have h2 : (x ^ n : ℝ) ^ 2 + (y ^ n : ℝ) ^ 2 = 1000 := by
    have h3 : x ^ (2 * n) = (x ^ n) ^ 2 := by ring_nf
    have h4 : y ^ (2 * n) = (y ^ n) ^ 2 := by ring_nf
    rw [h3, h4] at heq1
    linarith 
  have h5 : (x ^ n : ℝ) + (y ^ n : ℝ) = t := by linarith [heq2]
  have h6 : 0 < (x ^ n : ℝ) := by positivity
  have h7 : 0 < (y ^ n : ℝ) := by positivity
  have h8 : t ^ 2 = 1000 + 2 * ((x ^ n : ℝ) * (y ^ n : ℝ)) := by
    calc
      t ^ 2 = ((x ^ n : ℝ) + (y ^ n : ℝ)) ^ 2 := by
        rw [h5]
      _ = (x ^ n : ℝ) ^ 2 + (y ^ n : ℝ) ^ 2 + 2 * ((x ^ n : ℝ) * (y ^ n : ℝ)) := by
        ring
      _ = 1000 + 2 * ((x ^ n : ℝ) * (y ^ n : ℝ)) := by
        linarith [h2]
  -- Show 10 * sqrt 10 < t
  -- Need t > 0
  have h10 : 0 < t := by 
    have h11 : (x ^ n : ℝ) > 0 := h6
    have h12 : (y ^ n : ℝ) > 0 := h7
    have h13 : (x ^ n : ℝ) + (y ^ n : ℝ) > 0 := by
      linarith
    linarith [h5]
  have h9 : t ^ 2 > 1000 := by
    have h9 : (0: ℝ) < (x ^ n : ℝ) * (y ^ n : ℝ) := by
      apply mul_pos
      all_goals linarith
    nlinarith 
  have h12 : t > 10 * Real.sqrt 10 := by
    have h13 : t ^ 2 > 1000 := h9 
    -- We need (10 * sqrt 10) ^ 2 = 1000
    have h14 : (10 * Real.sqrt 10) ^ 2 = 1000 := by
      calc
        (10 * Real.sqrt 10) ^ 2 = 100 * (Real.sqrt 10) ^ 2 := by ring 
        _ = 100 * 10 := by 
          rw [Real.sq_sqrt]
          all_goals norm_num 
        _ = 1000 := by norm_num 
    nlinarith [Real.sqrt_nonneg 10, h10, sq_nonneg (t - 10 * Real.sqrt 10)]
  -- Show t ≤ 20 * sqrt 5
  have h11 : t ^ 2 ≤ 2000 := by 
    nlinarith [sq_nonneg ((x ^ n : ℝ) - (y ^ n : ℝ)), h2]
  have h14 : t ≤ 20 * Real.sqrt 5 := by
    -- We need (20 * sqrt 5) ^ 2 = 2000
    have h16 : (20 * Real.sqrt 5) ^ 2 = 2000 := by 
      calc 
        (20 * Real.sqrt 5) ^ 2 = 400 * (Real.sqrt 5) ^ 2 := by ring 
        _ = 400 * 5 := by 
          rw [Real.sq_sqrt]
          all_goals norm_num 
        _ = 2000 := by norm_num 
    nlinarith [Real.sqrt_nonneg 5, h10, sq_nonneg (t - 20 * Real.sqrt 5)]
  constructor
  · -- Show 10 * sqrt 10 < t
    linarith 
  · -- Show t ≤ 20 * sqrt 5
    linarith