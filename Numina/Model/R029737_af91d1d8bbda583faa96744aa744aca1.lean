import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316645 (f : ℝ → ℝ) (hf : f = λ x => -4 * x + 3 * sqrt (4 * x ^ 2 + 1)) :
    IsLeast {y | ∃ x, y = f x} (sqrt 5) := by
  constructor
  · -- Show that sqrt 5 is in the image of f
    use Real.sqrt 5 / 5
    rw [hf]
    have h1 : sqrt (4 * (sqrt 5 / 5) ^ 2 + 1) = 3 * sqrt 5 / 5 := by
      have h2 : 4 * (sqrt 5 / 5) ^ 2 + 1 = 9 / 5 := by
        have h3 : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
        nlinarith [Real.sqrt_nonneg 5, h3]
      rw [h2]
      have h4 : sqrt ((9 / 5 : ℝ)) = 3 * sqrt 5 / 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num [Real.mul_self_sqrt]
      exact h4
    simp [h1]
    <;> ring_nf <;> norm_num [Real.sq_sqrt, Real.sqrt_nonneg]
  · -- Show that sqrt 5 is the smallest value in the image
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h2 : sqrt (4 * x ^ 2 + 1) ≥ 0 := by positivity
    have h0 : -4 * x + 3 * sqrt (4 * x ^ 2 + 1) ≥ Real.sqrt 5 := by
      nlinarith [sq_nonneg (x - Real.sqrt 5 / 5), sq_nonneg (x + Real.sqrt 5 / 5),
        Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
        sq_nonneg (4 * x / 5 - 3 * Real.sqrt 5 / 5 / 5), sq_nonneg (sqrt (4 * x ^ 2 + 1) - 3 * Real.sqrt 5 / 5),
        Real.sqrt_nonneg (4 * x ^ 2 + 1), sq_nonneg (x * Real.sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * x ^ 2 + 1) by positivity)]
    linarith