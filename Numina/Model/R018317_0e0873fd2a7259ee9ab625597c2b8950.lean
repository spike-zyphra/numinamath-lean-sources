import Mathlib

open Real Set

theorem algebra_5046 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 2 + 8 * x + 33 - 3 * sqrt (x ^ 2 + 4 * x + 9)) :
    IsLeast (range f) (25 - 3 * sqrt 5) := by
  have h1 : ∀ x, f x = 2 * x ^ 2 + 8 * x + 33 - 3 * sqrt (x ^ 2 + 4 * x + 9) := by 
    intro x 
    rw [hf]

  have h2 : 25 - 3 * sqrt 5 ∈ range f := by
    use -2
    rw [h1]
    have h3 : ((-2 : ℝ) ) ^ 2 + 4 * (-2) + 9 = (5 : ℝ) := by norm_num
    have h4 : sqrt (( (-2 : ℝ) ) ^ 2 + 4 * (-2) + 9) = sqrt 5 := by 
      rw [h3]
    rw [h4]
    norm_num 
  have h5 : ∀ y, y ∈ range f → 25 - 3 * sqrt 5 ≤ y := by
    intro y hy 
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    have h6 : x ^ 2 + 4 * x + 9 = (x + 2) ^ 2 + 5 := by 
      nlinarith 
    have h7 : sqrt (x ^ 2 + 4 * x + 9) = sqrt ((x + 2) ^ 2 + 5) := by 
      rw [h6]
    rw [h7] at hx 
    have h8 : 2 * x ^ 2 + 8 * x + 33 = 2 * ((x + 2) ^ 2) + 25 := by 
      nlinarith 
    have h9 : 2 * x ^ 2 + 8 * x + 33 - 3 * sqrt ((x + 2) ^ 2 + 5) ≥ 25 - 3 * sqrt 5 := by
      nlinarith [Real.sqrt_nonneg ((x + 2) ^ 2 + 5), Real.sqrt_nonneg (5), 
        sq_nonneg (sqrt ((x + 2) ^ 2 + 5) - sqrt 5), 
        sq_nonneg ((x + 2) ^ 2), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ ((x + 2) ^ 2 + 5) by positivity), 
        Real.sqrt_le_sqrt (show (5 : ℝ) ≤ ( (x + 2) ^ 2 + 5) by nlinarith [sq_nonneg (x + 2)]), 
        mul_nonneg (Real.sqrt_nonneg (5)) (Real.sqrt_nonneg ((x + 2) ^ 2 + 5)), 
        sq_nonneg ( (x + 2) )
      ]
    linarith 
  constructor 
  · exact h2 
  · intro y hy 
    have h8 := h5 y hy 
    linarith [h8]