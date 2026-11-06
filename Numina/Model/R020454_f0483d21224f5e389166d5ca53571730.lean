import Mathlib
open Real Set

theorem algebra_8678 {f : ℝ → ℝ} (hf : f = λ x => x^2 - x + sqrt (2 * x^4 - 6 * x^2 + 8 * x + 16)) :
    IsLeast (range f) 4 := by
  have h1 : ∀ x, f x = x^2 - x + sqrt (2 * x^4 - 6 * x^2 + 8 * x + 16) := by
    intro x 
    rw [hf]

  constructor
  · -- Show 4 is achievable, which specific points gives 4
    use (0 : ℝ)
    rw [h1]
    have h41 : sqrt (2 * (0 : ℝ) ^ 4 - 6 * (0 : ℝ) ^ 2 + 8 * (0 : ℝ) + 16) = (4 : ℝ) := by 
      have h42 : (2 * (0 : ℝ) ^ 4 - 6 * (0 : ℝ) ^ 2 + 8 * (0 : ℝ) + 16 : ℝ) = (16 : ℝ) := by 
        norm_num 
      rw [h42] 
      have h43 : sqrt (16 : ℝ) = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h43]
    simp only [h41] 
    all_goals norm_num 
  · -- Show all y in range f satisfies y >= 4
    intro y 
    rintro ⟨x, hx⟩
    rw [h1 x] at hx
    have h3 : x^2 - x + sqrt (2 * x^4 - 6 * x^2 + 8 * x + 16) ≥ 4 := by 
      by_cases h9 : 4 - x^2 + x ≤ 0 
      · -- Case where 4 - (x ^ 2) + x ≤ 0 
        have h5 : x^2 - x ≥ 0 := by nlinarith 
        have h6 : sqrt (2 * x^4 - 6 * x^2 + 8 * x + 16) ≥ 0 := Real.sqrt_nonneg (2 * x^4 - 6 * x^2 + 8 * x + 16)
        nlinarith [Real.sqrt_nonneg (2 * x^4 - 6 * x^2 + 8 * x + 16), 
              Real.sq_sqrt (show (2 * x^4 - 6 * x^2 + 8 * x + 16 ) ≥ 0 by 
                nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x + 2)]
              )
           ]
      · -- Case where 4 - (x ^ 2) + x > 0 
        have h7 : sqrt (2 * x^4 - 6 * x^2 + 8 * x + 16) ≥ 4 - x^2 + x := by
          have h8 : 2 * x^4 - 6 * x^2 + 8 * x + 16 ≥ (4 - x^2 + x)^2 := by 
            nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 0), sq_nonneg (x^2 - 2), sq_nonneg (x * (x + 1))]
          have h9 : sqrt (2 * x^4 - 6 * x^2 + 8 * x + 16) ≥ sqrt ((4 - x^2 + x)^2) := Real.sqrt_le_sqrt (show (4 - x^2 + x)^2 ≤ 2 * x^4 - 6 * x^2 + 8 * x + 16 by linarith)
          have h10 : sqrt ((4 - x^2 + x)^2) = 4 - x^2 + x := by 
            rw [Real.sqrt_sq]
            linarith 
          linarith [h9, h10]
        nlinarith [Real.sqrt_nonneg (2 * x^4 - 6 * x^2 + 8 * x + 16), 
              Real.sq_sqrt (show (2 * x^4 - 6 * x^2 + 8 * x + 16 ) ≥ 0 by 
                nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x + 2)]
              )
           ]
    linarith [h3, hx]