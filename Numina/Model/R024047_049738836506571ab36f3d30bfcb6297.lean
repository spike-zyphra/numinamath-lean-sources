import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_110123 (f : ℝ → ℝ) (hf : f = λ x => sqrt (x^2 + 4) + sqrt (x^2 + 2 * x + 10)) :
    IsLeast (range f) (sqrt 26) := by
  have h1 : ∀ x, f x = sqrt (x ^ 2 + 4) + sqrt (x ^ 2 + 2 * x + 10) := by 
    intro x 
    rw [hf]

  have h2 : sqrt 26 ∈ range f := by 
    use (-2 / 5)
    rw [h1]
    have h3 : sqrt ((-2 / 5 : ℝ) ^ 2 + 4) = (2 / 5) * sqrt 26 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h4 : sqrt ((-2 / 5 : ℝ) ^ 2 + 2 * (-2 / 5) + 10) = (3 / 5) * sqrt 26 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3, h4]
    ring

  have h5 : sqrt 26 ∈ lowerBounds (range f) := by 
    intro y hy 
    rcases hy with ⟨x, hx⟩ 
    rw [h1 x] at hx 
    have h6 : sqrt (x ^ 2 + 4) + sqrt (x ^ 2 + 2 * x + 10) ≥ sqrt 26 := by 
      have h7 : (sqrt (x ^ 2 + 4) + sqrt (x ^ 2 + 2 * x + 10)) ^ 2 ≥ (sqrt 26) ^ 2 := by 
        have h8 : (sqrt (x ^ 2 + 4) + sqrt (x ^ 2 + 2 * x + 10)) ^ 2 = 
              (sqrt (x ^ 2 + 4)) ^ 2 + (sqrt (x ^ 2 + 2 * x + 10)) ^ 2 + 2 * (sqrt (x ^ 2 + 4) * sqrt (x ^ 2 + 2 * x + 10)) := by 
          ring
        have h9 : (sqrt (x ^ 2 + 4)) ^ 2 = x ^ 2 + 4 := by 
          apply Real.sq_sqrt 
          positivity
        have h10 : (sqrt (x ^ 2 + 2 * x + 10)) ^ 2 = x ^ 2 + 2 * x + 10 := by 
          apply Real.sq_sqrt 
          nlinarith
        rw [h8, h9, h10]
        have h11 : (sqrt 26) ^ 2 = (26 : ℝ) := Real.sq_sqrt (by norm_num)
        nlinarith [sq_nonneg (x + 2 / 5), sq_nonneg ((x ^ 2 + 4) - (x ^ 2 + 2 * x + 10)), 
                  sq_nonneg ((x + 2 / 5) * 3 - 2), 
                  Real.sqrt_nonneg (x^2 + 4), Real.sqrt_nonneg (x^2 + 2 * x + 10), 
                  mul_nonneg (Real.sqrt_nonneg (x^2 + 4)) (Real.sqrt_nonneg (x^2 + 2 * x + 10)), 
                  Real.sq_sqrt (show (x ^ 2 + 4 : ℝ) ≥ 0 by positivity), 
                  Real.sq_sqrt (show (x ^ 2 + 2 * x + 10 : ℝ) ≥ 0 by nlinarith), 
                  mul_self_nonneg (x + 1)
                ]
      have h8 : sqrt (x ^ 2 + 4) + sqrt (x ^ 2 + 2 * x + 10) ≥ 0 := by 
        positivity
      have h9 : sqrt 26 ≥ 0 := by 
        positivity
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 4), Real.sqrt_nonneg (x ^ 2 + 2 * x + 10), h9, h7]
    linarith [h6, Real.sqrt_nonneg 26]

  constructor 
  · exact h2 
  · exact h5