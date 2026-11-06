import Mathlib

open Real Set

theorem algebra_13984 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x^2 + 4 * x + 5) + sqrt (x^2 - 8 * x + 25)) :
    IsLeast {y | ∃ x, y = f x} (2 * sqrt 13) := by
  constructor
  · -- Show that 2 * sqrt 13 is achievable, by x = -1 / 2
    use -1 / 2
    rw [hf]
    have h1 : (-1 / 2 : ℝ) ^ 2 + 4 * (-1 / 2 : ℝ) + 5 = (13 / 4 : ℝ) := by norm_num
    have h2 : (-1 / 2 : ℝ) ^ 2 - 8 * (-1 / 2 : ℝ) + 25 = (117 / 4 : ℝ) := by norm_num
    simp only [h1, h2]
    have h3 : sqrt ((13 / 4 : ℝ)) = Real.sqrt (13) / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h4 : sqrt ((117 / 4 : ℝ)) = 3 * Real.sqrt (13) / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3, h4]
    ring_nf <;> norm_num
  · -- Show that 2 * sqrt 13 is minimal
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h5 : sqrt (x^2 + 4 * x + 5) + sqrt (x^2 - 8 * x + 25) ≥ 2 * sqrt 13 := by
      have h1 : (x ^ 2 + 4 * x + 5) ≥ 0 := by 
        nlinarith [sq_nonneg (x + 2)]
      have h2 : (x ^ 2 - 8 * x + 25) ≥ 0 := by 
        nlinarith [sq_nonneg (x - 4)]
      have h3 : (sqrt (x^2 + 4 * x + 5) + sqrt (x^2 - 8 * x + 25)) ^ 2 ≥ (2 * sqrt 13) ^ 2 := by
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 4 * x + 5) - sqrt (x ^ 2 - 8 * x + 25)), 
                  sq_nonneg (x + 1 / 2), 
                  Real.sqrt_nonneg (x ^ 2 + 4 * x + 5), 
                  Real.sqrt_nonneg (x ^ 2 - 8 * x + 25), 
                  mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 4 * x + 5)) (Real.sqrt_nonneg (x ^ 2 - 8 * x + 25)), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 4 * x + 5 by nlinarith [sq_nonneg (x + 2)]), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 8 * x + 25 by nlinarith [sq_nonneg (x - 4)]), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)
                ]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 4 * x + 5), Real.sqrt_nonneg (x ^ 2 - 8 * x + 25), Real.sqrt_nonneg (13), mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 4 * x + 5)) (Real.sqrt_nonneg (x ^ 2 - 8 * x + 25)), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    linarith [h5]