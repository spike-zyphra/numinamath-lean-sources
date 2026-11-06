import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314280 (f : ℝ → ℝ) (hf : f = λ x => sqrt (x - 4) + sqrt (15 - 3 * x)) :
    ∀ x ∈ Icc 4 5, f x ∈ Icc 1 2 := by

  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have hfx1 : f x = sqrt (x - 4) + sqrt (15 - 3 * x) := by 
    rw [hf]

  have h1 : 0 ≤ x - 4 := by linarith
  have h2 : 0 ≤ 15 - 3 * x := by
    nlinarith

  have h3 : sqrt (x - 4) ≥ 0 := Real.sqrt_nonneg (x - 4)
  have h4 : sqrt (15 - 3 * x) ≥ 0 := Real.sqrt_nonneg (15 - 3 * x)

  have h5 : 1 ≤ sqrt (x - 4) + sqrt (15 - 3 * x) := by
    nlinarith [sq_nonneg (sqrt (x - 4) - 1), sq_nonneg (sqrt (15 - 3 * x) - 1.5), 
          Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg (x - 4)) (Real.sqrt_nonneg (15 - 3 * x)), 
          mul_nonneg (show (0 : ℝ) ≤ x - 4 by linarith) (show (0 : ℝ) ≤ 15 - 3 * x by linarith)
    ]

  have h6 : sqrt (x - 4) + sqrt (15 - 3 * x) ≤ 2 := by 
    nlinarith [sq_nonneg (sqrt (x - 4) - 0.5), sq_nonneg (sqrt (15 - 3 * x) - 1.5), 
          Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg (x - 4)) (Real.sqrt_nonneg (15 - 3 * x)), 
          mul_nonneg (show (0 : ℝ) ≤ x - 4 by linarith) (show (0 : ℝ) ≤ 15 - 3 * x by linarith)
    ]

  rw [hfx1]
  constructor
  · -- Show that 1 ≤ f(x)
    linarith [h5]
  · -- Show that f(x) ≤ 2
    linarith [h6]