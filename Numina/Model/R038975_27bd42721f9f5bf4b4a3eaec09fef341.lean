import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12257 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) :
  IsGreatest (range f) (sqrt 2) := by
  constructor
  · -- Show that sqrt(2) is attained by f
    use Real.sqrt (2 / 3)
    have h1 : (Real.sqrt (2 / 3) : ℝ) ^ 2 = (2 / 3 : ℝ) := Real.sq_sqrt (by norm_num)
    have h2 : (Real.sqrt (2 / 3) : ℝ) ^ 4 = ( (Real.sqrt (2 / 3) : ℝ) ^ 2 ) ^ 2 := by ring
    rw [h₀]
    rw [h2, h1]
    have h3 : ((2 / 3 : ℝ) ) - ( (2 / 3 : ℝ) ) ^ 2 = (2 / 9 : ℝ) := by norm_num
    have h4 : (2 * (2 / 3 : ℝ) ) - ( (2 / 3 : ℝ) ) ^ 2 = (8 / 9 : ℝ) := by norm_num
    have h5 : sqrt (( (2 / 3 : ℝ) ) - ( (2 / 3 : ℝ) ) ^ 2 ) = sqrt (2 / 9 : ℝ) := by rw [h3]
    have h6 : sqrt (2 * ( (2 / 3 : ℝ) ) - ( (2 / 3 : ℝ) ) ^ 2 ) = sqrt (8 / 9 : ℝ) := by rw [h4]
    rw [h5, h6]
    have h7 : sqrt (2 / 9 : ℝ) = Real.sqrt 2 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h8 : sqrt (8 / 9 : ℝ) = 2 * Real.sqrt 2 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h7, h8]
    ring
  · -- Show that sqrt(2) is greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀] at hx
    have hx1 : sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4) ≤ Real.sqrt 2 := by 
      by_cases h1 : x ^ 2 ≤ 1
      · -- Case where x^2 ≤ 1
        have h2 : x ^ 2 - x ^ 4 ≥ 0 := by 
          nlinarith [sq_nonneg (x ^ 2 - 1), h1]
        have h3 : 2 * x ^ 2 - x ^ 4 ≥ 0 := by 
          nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2), h1]
        have h4 : (sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2 ≤ 2 := by
          nlinarith [Real.sqrt_nonneg (x ^ 2 - x ^ 4), Real.sqrt_nonneg (2 * x ^ 2 - x ^ 4),
            sq_nonneg (sqrt (x ^ 2 - x ^ 4) - sqrt (2 * x ^ 2 - x ^ 4)), 
            sq_nonneg ((x ^ 2) - 2 / 3), 
            Real.sq_sqrt (show x ^ 2 - x ^ 4 ≥ 0 by linarith), 
            Real.sq_sqrt (show 2 * x ^ 2 - x ^ 4 ≥ 0 by linarith), 
            mul_nonneg (Real.sqrt_nonneg (x ^ 2 - x ^ 4)) (Real.sqrt_nonneg (2 * x ^ 2 - x ^ 4)), 
            sq_nonneg (x^2 -1)]
        have h5 : sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4) ≤ Real.sqrt 2 := by 
          have h6 : (sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2 ≤ 2 := h4
          have h7 : sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4) ≥ 0 := by 
            positivity
          have h8 : Real.sqrt 2 ≥ 0 := by positivity
          have h9 : (sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
            linarith [h6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          nlinarith [h7, h8, Real.sqrt_nonneg 2, h9]
        linarith [h5, Real.sqrt_nonneg 2]
      · -- Case where x^2 > 1
        have h2 : x ^ 2 > 1 := by linarith 
        have h6 : x ^ 2 - x ^ 4 ≤ 0 := by
          nlinarith [sq_nonneg (x ^ 2 - 1), h2]
        have h8 : sqrt (x^2 - x^4) = 0 := by
          rw [Real.sqrt_eq_zero']
          linarith 
          all_goals nlinarith 
        by_cases h3 : (2 * x ^ 2 - x^4) ≥ 0 
        · -- Case where 2 *x^2 -x^4 ≥0
          have h7 : sqrt (2 * x ^ 2 -x^4) ≥ 0 := by positivity 
          have h9 : sqrt (2 * x ^ 2 -x^4) ≤ Real.sqrt 2 := by 
            have h10 : (2 * x ^ 2 - x^4) ≤ 2 := by 
              nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2), h2]
            have h11 : sqrt (2 * x ^ 2 -x^4) ≤ sqrt (2 : ℝ) := by 
              apply Real.sqrt_le_sqrt 
              linarith 
            linarith 
          have hx2 : sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 -x^4) = sqrt (2 *x^2 -x^4) := by 
            rw [h8] 
            all_goals linarith 
          linarith [hx2, h9, Real.sqrt_nonneg 2]
        · -- Case where 2 *x^2 -x^4 <0 
          have h7 : 2 * x ^ 2 -x^4 < (0 : ℝ) := by linarith 
          have h9 : sqrt (2 * x ^ 2 -x^4) =0 := by 
            rw [Real.sqrt_eq_zero'] 
            linarith 
            all_goals linarith 
          linarith [h8, h9, Real.sqrt_nonneg 2]
    linarith [hx, hx1, Real.sqrt_nonneg 2]