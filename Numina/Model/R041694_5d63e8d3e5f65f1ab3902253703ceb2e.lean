import Mathlib

open Real Set

theorem algebra_280626 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x^2 - 8 * x + 25) + sqrt (x^2 - 4 * x + 13)) :
    IsLeast (range f) (2 * sqrt 10) := by
  have h1 : ∀ x, f x = sqrt (x^2 - 8 * x + 25) + sqrt (x^2 - 4 * x + 13) := by
    intro x
    rw [hf]

  have h2 : 2 * sqrt 10 ∈ range f := by
    use 3
    rw [h1]
    have h3 : (3 : ℝ) ^ 2 - 8 * (3 : ℝ) + 25 = (10 : ℝ) := by norm_num
    have h4 : (3 : ℝ) ^ 2 - 4 * (3 : ℝ) + 13 = (10 : ℝ) := by norm_num
    have h5 : sqrt ((3 : ℝ) ^ 2 - 8 * (3 : ℝ) + 25) = sqrt 10 := by rw [h3]
    have h6 : sqrt ((3 : ℝ) ^ 2 - 4 * (3 : ℝ) + 13) = sqrt 10 := by rw [h4]
    rw [h5, h6]
    ring

  have h7 : ∀ y, y ∈ range f → 2 * sqrt 10 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    have h10 : sqrt (x^2 - 8 * x + 25) + sqrt (x^2 - 4 * x + 13) ≥ 2 * sqrt 10 := by
      have h11 : sqrt (x ^ 2 - 8 * x + 25) ≥ 0 := by apply Real.sqrt_nonneg
      have h12 : sqrt (x ^ 2 - 4 * x + 13) ≥ 0 := by apply Real.sqrt_nonneg
      have h13 : (sqrt (x ^ 2 - 8 * x + 25) + sqrt (x ^ 2 - 4 * x + 13)) ^ 2 ≥ (2 * sqrt 10) ^ 2 := by
        nlinarith [Real.sqrt_nonneg ((x ^ 2 - 8 * x + 25) ), Real.sqrt_nonneg ((x ^ 2 - 4 * x + 13) ), 
          Real.sqrt_nonneg (10), 
          sq_nonneg (sqrt (x ^ 2 - 8 * x + 25) - sqrt (x ^ 2 - 4 * x + 13)), 
          sq_nonneg (x - 3), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 8 * x + 25 by nlinarith [sq_nonneg (x - 4)]), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 4 * x + 13 by nlinarith [sq_nonneg (x - 2)]), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (10: ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 - 8 * x + 25)) (Real.sqrt_nonneg (x ^ 2 - 4 * x + 13)), 
          Real.sqrt_le_sqrt (show (10 : ℝ) ≤ (x ^ 2 - 8 * x + 25) + (x ^ 2 - 4 * x + 13) by nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 4), sq_nonneg (x - 2)] )
          ]
      nlinarith [Real.sqrt_nonneg ((x ^ 2 - 8 * x + 25) ), Real.sqrt_nonneg ((x ^ 2 - 4 * x + 13) ), Real.sqrt_nonneg 10, h13, sq_nonneg (sqrt (x ^ 2 - 8 * x + 25) + sqrt (x ^ 2 - 4 * x + 13) - 2 * sqrt 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10: ℝ) by norm_num)]
    nlinarith [h10, hx]

  constructor
  · exact h2
  · intro y hy
    exact h7 y hy