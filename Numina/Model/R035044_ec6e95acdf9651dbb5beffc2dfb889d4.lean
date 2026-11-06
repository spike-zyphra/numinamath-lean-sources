import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_234065 {f : ℝ → ℝ}
  (hf : f = λ x => (sqrt (x^2 + 1) + x - 1) / (sqrt (x^2 + 1) + x + 1)) :
  Odd f ∧ ∀ x, f x ∈ Ioo (-1) 1 := by
  constructor 
  · -- Show f is odd
    use (fun x => (-1 / (sqrt (x^2 + 1) + x + 1)))
    funext x 
    rw [hf]
    have h1 : sqrt (x ^ 2 + 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 1)
    have h6 : (sqrt (x ^ 2 +1) +x+1) ≠0 := by
      have h5 : sqrt (x ^2 +1) ≥0 := Real.sqrt_nonneg (x ^2+1)
      nlinarith [Real.sqrt_nonneg (x^2 +1), sq_nonneg x, Real.sq_sqrt (show 0 ≤ (x^2+1 : ℝ) by positivity)]
    field_simp [h6] 
    <;> nlinarith [Real.sqrt_nonneg (x ^ 2 +1), Real.sq_sqrt (show 0 ≤ (x ^ 2 +1 : ℝ) by positivity)]
  · -- Show the range is (-1, 1)
    intro x
    rw [hf]
    have h10 : (sqrt (x ^ 2 +1) +x -1) / (sqrt (x^2 +1) +x+1) > -1 := by
      have h5 : sqrt (x ^ 2 +1) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith [sq_nonneg x] 
      apply (lt_div_iff₀ (by 
        nlinarith [Real.sqrt_nonneg (x ^ 2 +1), sq_nonneg (x), sq_nonneg (sqrt (x ^ 2 +1)+x+1), Real.sq_sqrt (show 0 ≤ (x^2 +1: ℝ) by positivity)]
      )).mpr 
      nlinarith [Real.sqrt_nonneg (x ^ 2 +1), Real.sq_sqrt (show 0 ≤ (x^2 +1: ℝ) by positivity), sq_nonneg (x+1), sq_nonneg (sqrt (x ^ 2 +1)-1), sq_nonneg (x-1)]
    have h2 : (sqrt (x ^ 2 +1) +x -1) / (sqrt (x ^ 2 +1) +x+1) < 1 := by
      have h5 : sqrt (x ^ 2 +1) > 0 := by
        apply Real.sqrt_pos.mpr 
        nlinarith [sq_nonneg x] 
      apply (div_lt_iff₀ (by
        nlinarith [Real.sqrt_nonneg (x^2+1), sq_nonneg (x), sq_nonneg (sqrt (x^2+1)+x+1), Real.sq_sqrt (show 0 ≤ (x^2 +1 : ℝ) by positivity)]
      )).mpr 
      nlinarith [Real.sqrt_nonneg (x^2+1), Real.sq_sqrt (show 0 ≤ (x^2+1 : ℝ) by positivity), sq_nonneg (x +1), sq_nonneg (sqrt (x^2+1) -1), sq_nonneg (x-1)]
    simp at *
    constructor <;> linarith