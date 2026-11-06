import Mathlib

open Real Set

theorem algebra_204575 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = sqrt (x ^ 2 + (x + 1) ^ 2) + sqrt (x ^ 2 + (x - 1) ^ 2)) :
    IsLeast {y | ∃ x, y = f x} (f 0) := by
  have h1 : f 0 = 2 := by
    rw [h₀ 0]
    have h2 : sqrt (0 ^ 2 + (0 + 1) ^ 2) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : sqrt (0 ^ 2 + (0 - 1) ^ 2) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2, h3]
    all_goals norm_num
  constructor
  · -- Show that f(0) is indeed in the set
    use 0
  · -- Show that f(0) is the minimum value
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀ x] at hx
    have h6 : sqrt (x ^ 2 + (x + 1) ^ 2) + sqrt (x ^ 2 + (x - 1) ^ 2) ≥ (2 : ℝ) := by
      have h7 : sqrt (x ^ 2 + (x + 1) ^ 2) ≥ 0 := by positivity
      have h8 : sqrt (x ^ 2 + (x - 1) ^ 2) ≥ 0 := by positivity
      have h11 : (sqrt (x ^ 2 + (x + 1) ^ 2) + sqrt (x ^ 2 + (x - 1) ^ 2)) ^ 2 ≥ (2 : ℝ) ^ 2 := by
        have h9 : (sqrt (x ^ 2 + (x + 1) ^ 2)) ^ 2 = x ^ 2 + (x + 1) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith 
        have h10 : (sqrt (x ^ 2 + (x - 1) ^ 2)) ^ 2 = x ^ 2 + (x - 1) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith 
        have h12 : (sqrt (x ^ 2 + (x + 1) ^ 2) + sqrt (x ^ 2 + (x - 1) ^ 2)) ^ 2 =
            (sqrt (x ^ 2 + (x + 1) ^ 2)) ^ 2 + (sqrt (x ^ 2 + (x - 1) ^ 2)) ^ 2 + 2 * (sqrt (x ^ 2 + (x + 1) ^ 2) * sqrt (x ^ 2 + (x - 1) ^ 2)) := by
          ring
        rw [h12, h9, h10]
        nlinarith [sq_nonneg (sqrt (x ^ 2 + (x + 1) ^ 2) - sqrt (x ^ 2 + (x - 1) ^ 2)), sq_nonneg (x), sq_nonneg ((x + 1) - (x - 1)), Real.sqrt_nonneg (x ^ 2 + (x + 1) ^ 2), Real.sqrt_nonneg (x ^ 2 + (x - 1) ^ 2),
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + (x + 1) ^ 2)) (Real.sqrt_nonneg (x ^ 2 + (x - 1) ^ 2)),
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + (x + 1) ^ 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + (x - 1) ^ 2 by nlinarith)
        ]
      have h13 : sqrt (x ^ 2 + (x + 1) ^ 2) + sqrt (x ^ 2 + (x - 1) ^ 2) ≥ (2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (x ^ 2 + (x + 1) ^ 2), Real.sqrt_nonneg (x ^ 2 + (x - 1) ^ 2), sq_nonneg (sqrt (x ^ 2 + (x + 1) ^ 2) + sqrt (x ^ 2 + (x - 1) ^ 2) - (2 : ℝ)), sq_nonneg (sqrt (x ^ 2 + (x + 1) ^ 2) - sqrt (x ^ 2 + (x - 1) ^ 2))
        ]
      linarith
    linarith [h1, h6, hx]