import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_165528 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = (2 * x - y) ^ 2 - 2 * y ^ 2 - 3 * y)
  (x : ℝ) (hx : ∀ y, f x y ≤ f (-3 / 8) y) :
  x = -3 / 8 := by

  have h1 := hx 0
  have h1' : f x 0 ≤ f (-3 / 8) 0 := by simpa using h1
  rw [h₀, h₀] at h1'
  -- This gives the inequality: (2 * x) ^ 2 ≤ (-3/4) ^ 2, i.e., 4 * x^2 ≤ 9/16
  have h1x : 4 * x ^ 2 ≤ 9 / 16 := by
    nlinarith
  
  have h2 := hx (-1)
  have h2' : f x (-1) ≤ f (-3 / 8) (-1) := by simpa using h2
  rw [h₀, h₀] at h2'
  -- This leads to the inequality: 4 * x^2 + 4 * x + 2 ≤ 17/16
  -- Multiplying by 16: 64 * x^2 + 64 * x + 32 ≤ 17, simplifies to: 64 * x^2 + 64 * x + 15 ≤ 0
  have h2x : 64 * x ^ 2 + 64 * x + 15 ≤ 0 := by
    nlinarith
  
  have h3x : x ≥ -3 / 8 := by
    nlinarith [sq_nonneg (x + 3 / 8), sq_nonneg (x - 3 / 8)]

  have h4x : x ≤ -3 / 8 := by
    nlinarith [sq_nonneg (x + 3 / 8), sq_nonneg (x - 3 / 8)]

  linarith