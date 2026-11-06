import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_173808 (f : ℝ → ℝ)
  (hf : f = λ x => x^2 - x + sqrt (2*x^4 - 6*x^2 + 8*x + 16)) :
  IsLeast (range f) 4 := by
  unfold IsLeast
  constructor
  · -- Show 4 is achievable via x = 0
    use 0
    rw [hf]
    norm_num [Real.sqrt_eq_iff_sq_eq]
  · -- Show that 4 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h5 : (2 * x ^ 4 - 6 * x ^ 2 + 8 * x + 16) ≥  0 := by
      nlinarith [sq_nonneg (x ^ 2 + 2 * x - 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x * (x + 1)), sq_nonneg ((x ^ 2 + 2 * x) - 4)]
    have h1 : Real.sqrt (2 * x ^ 4 - 6 * x ^ 2 + 8 * x + 16) ≥ 0 := Real.sqrt_nonneg _
    have h7 : (Real.sqrt (2 * x ^ 4 - 6 * x ^ 2 + 8 * x + 16)) ^ 2 = 2 * x ^ 4 - 6 * x ^ 2 + 8 * x + 16 := Real.sq_sqrt (by nlinarith)
    nlinarith [ sq_nonneg (Real.sqrt (2 * x ^ 4 - 6 * x ^ 2 + 8 * x + 16) - 2), sq_nonneg (x ^ 2 - (x + 1) ^ 2), sq_nonneg (x + 1), sq_nonneg (x^2 + x - 2), Real.sqrt_nonneg (2 * x ^ 4 - 6 * x ^ 2 + 8 * x + 16) ]