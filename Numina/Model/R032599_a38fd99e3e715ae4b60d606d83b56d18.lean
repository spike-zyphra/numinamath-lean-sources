import Mathlib

open Real

theorem inequalities_56778 (x : Fin 5 → ℝ)
    (h₀ : ∀ i, 0 ≤ x i)
    (h₁ : x 0 ≤ 4)
    (h₂ : x 0 + x 1 ≤ 13)
    (h₃ : x 0 + x 1 + x 2 ≤ 29)
    (h₄ : x 0 + x 1 + x 2 + x 3 ≤ 54)
    (h₅ : x 0 + x 1 + x 2 + x 3 + x 4 ≤ 90) :
    sqrt (x 0) + sqrt (x 1) + sqrt (x 2) + sqrt (x 3) + sqrt (x 4) ≤ 20 := by
  have h1 : 0 ≤ x 0 := h₀ 0
  have h2 : 0 ≤ x 1 := h₀ 1
  have h3 : 0 ≤ x 2 := h₀ 2
  have h4 : 0 ≤ x 3 := h₀ 3
  have h5 : 0 ≤ x 4 := h₀ 4
  have h6 : sqrt (x 0) ≥ 0 := by positivity
  have h7 : sqrt (x 1) ≥ 0 := by positivity
  have h8 : sqrt (x 2) ≥ 0 := by positivity
  have h9 : sqrt (x 3) ≥ 0 := by positivity
  have h10 : sqrt (x 4) ≥ 0 := by positivity
  have h11 : (sqrt (x 0)) ^ 2 = x 0 := Real.sq_sqrt (show (0 : ℝ) ≤ x 0 by linarith)
  have h12 : (sqrt (x 1)) ^ 2 = x 1 := Real.sq_sqrt (show (0 : ℝ) ≤ x 1 by linarith)
  have h13 : (sqrt (x 2)) ^ 2 = x 2 := Real.sq_sqrt (show (0 : ℝ) ≤ x 2 by linarith)
  have h14 : (sqrt (x 3)) ^ 2 = x 3 := Real.sq_sqrt (show (0 : ℝ) ≤ x 3 by linarith)
  have h15 : (sqrt (x 4)) ^ 2 = x 4 := Real.sq_sqrt (show (0 : ℝ) ≤ x 4 by linarith)
  nlinarith [sq_nonneg (sqrt (x 0) - 2), sq_nonneg (sqrt (x 1) - 3), sq_nonneg (sqrt (x 2) - 4), sq_nonneg (sqrt (x 3) - 5), sq_nonneg (sqrt (x 4) - 6),
          Real.sqrt_nonneg (x 0), Real.sqrt_nonneg (x 1), Real.sqrt_nonneg (x 2), Real.sqrt_nonneg (x 3), Real.sqrt_nonneg (x 4),
          mul_nonneg (Real.sqrt_nonneg (x 0)) (Real.sqrt_nonneg (x 1)),
          mul_nonneg (Real.sqrt_nonneg (x 0)) (Real.sqrt_nonneg (x 2)),
          mul_nonneg (Real.sqrt_nonneg (x 0)) (Real.sqrt_nonneg (x 3)),
          mul_nonneg (Real.sqrt_nonneg (x 0)) (Real.sqrt_nonneg (x 4)),
          mul_nonneg (Real.sqrt_nonneg (x 1)) (Real.sqrt_nonneg (x 2)),
          mul_nonneg (Real.sqrt_nonneg (x 1)) (Real.sqrt_nonneg (x 3)),
          mul_nonneg (Real.sqrt_nonneg (x 1)) (Real.sqrt_nonneg (x 4)),
          mul_nonneg (Real.sqrt_nonneg (x 2)) (Real.sqrt_nonneg (x 3)),
          mul_nonneg (Real.sqrt_nonneg (x 2)) (Real.sqrt_nonneg (x 4)),
          mul_nonneg (Real.sqrt_nonneg (x 3)) (Real.sqrt_nonneg (x 4))
        ]