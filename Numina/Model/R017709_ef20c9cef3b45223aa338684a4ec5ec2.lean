import Mathlib

open Finset Real

theorem algebra_175603 {a : ℕ → ℤ} (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 1) = a n ^ 2 - a n + 1) :
    ∑ i ∈ range 2008, (1 / a (i + 1)) < 1 := by
  have h1 := han 0
  have h2 : a 1 = 2 := ha1 
  rw [show a 1 = 2 by linarith [ha1]] at h1 
  ring_nf at h1
  have h4 : a 0 ^ 2 - a 0 - 1 = 0 := by 
    nlinarith
  have h5 : a 0 ≤ 2 := by 
    nlinarith [sq_nonneg (a 0 - 2 : ℤ), sq_nonneg (a 0 + 1 : ℤ), sq_nonneg (a 0 : ℤ)]
  have h7 : a 0 ≥ 0 := by
    nlinarith [sq_nonneg (a 0 : ℤ), sq_nonneg (a 0 - 2 : ℤ), sq_nonneg (a 0 + 1 : ℤ)]
  interval_cases h8 : a 0 <;> omega