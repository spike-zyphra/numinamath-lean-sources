import Mathlib

open Real Set

theorem algebra_327796 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x^2 + 1) + sqrt ((4 - x)^2 + 4)) :
    IsLeast {y | ∃ x, f x = y} 5 := by 
  constructor
  -- Show 5 is in the image
  · -- Show 5 is attained at x = 4/3
    use 4 / 3 
    rw [hf] 
    have h1 : sqrt ((4 / 3) ^ 2 + 1) = 5 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : sqrt ((4 - (4 / 3)) ^ 2 + 4) = 10 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    simp [h1, h2]
    all_goals linarith
  -- Show there is no smaller value in the image
  · -- Let y ∈  image of f, prove 5 ≤ y
    rintro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    have h1 : sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4) ≥ 5 := by
      have h2 : (sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4)) ^ 2 ≥ 25 := by
        have h3 : sqrt (x ^ 2 + 1) ≥ 0 := by positivity
        have h4 : sqrt ((4 - x) ^ 2 + 4) ≥ 0 := by positivity
        have h5 : (sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4)) ^ 2 =
          (sqrt (x ^ 2 + 1)) ^ 2 + (sqrt ((4 - x) ^ 2 + 4)) ^ 2 + 2 * (sqrt (x ^ 2 + 1) * sqrt ((4 - x) ^ 2 + 4)) := by ring
        have h6 : (sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by nlinarith)
        have h7 : (sqrt ((4 - x) ^ 2 + 4)) ^ 2 = (4 - x) ^ 2 + 4 := Real.sq_sqrt (by nlinarith)
        have h9 : sqrt (x ^ 2 + 1) * sqrt ((4 - x) ^ 2 + 4) ≥ 0 := by positivity
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 1) - sqrt ((4 - x) ^ 2 + 4)), sq_nonneg (x - 4 / 3), 
          Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg ((4 - x) ^ 2 + 4), 
          h6, h7, 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg ((4 - x) ^ 2 + 4)), 
          sq_nonneg (sqrt (x ^ 2 + 1) * sqrt ((4 - x) ^ 2 + 4) - (x * (4 - x) + 1 * 2))
          ]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg ((4 - x) ^ 2 + 4), 
        sq_nonneg (sqrt (x ^ 2 + 1) - sqrt ((4 - x) ^ 2 + 4)), 
        sq_nonneg (x - 4 / 3), 
        Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (4 - x) ^ 2 + 4 by nlinarith)
      ]
    simp at hx
    nlinarith [h1, hx]