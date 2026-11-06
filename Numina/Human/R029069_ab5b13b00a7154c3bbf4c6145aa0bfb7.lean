import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600748 {a b c h : ℝ}
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (h₀ : a^2 + b^2 = c^2)
  (h₁ : h * c = a * b) -- this equation is for the height
  :
  2 * sqrt 2 / 3 * (c + h) ≤ a + b ∧ a + b < c + h := by

  have h2 : h > 0 := by nlinarith [mul_pos ha hb, hc]
  
  have h3 : a + b < c + h := by
    have h4 : c * (a + b) < c ^ 2 + a * b := by 
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h₀, h₁, mul_self_nonneg (a - b),
        sq_nonneg (a - c), sq_nonneg (b - c)]
    nlinarith
  
  have h5 : 2 * sqrt 2 / 3 * (c + h) ≤ a + b := by 
    have h6 : (2 * sqrt 2 / 3 * (c + h)) ^ 2 ≤ (a + b) ^ 2 := by
      have h7 : (2 * sqrt 2 / 3 * (c + h)) ^ 2 = (8 / 9) * (c + h) ^ 2 := by
        calc 
          (2 * sqrt 2 / 3 * (c + h)) ^ 2 
              = (2 * sqrt 2) ^ 2 / 9 * (c + h) ^ 2 := by ring 
          _ = (4 * (sqrt 2) ^ 2) / 9 * (c + h) ^ 2 := by ring 
          _ = (4 * 2) / 9 * (c + h) ^ 2 := by rw [Real.sq_sqrt]; linarith 
          _ = (8 / 9) * (c + h) ^ 2 := by ring 
      have h8 : (a + b) ^ 2 = a^2 + 2 * a * b + b^2 := by ring 
      have h9 : (8 / 9) * (c + h) ^ 2 ≤ (a + b) ^ 2 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - c ^ 2), sq_nonneg (a * c - b * c),
          h₀, h₁, sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      nlinarith [h7, h8, h9]
    
    have h10 : 2 * sqrt 2 / 3 * (c + h) ≤ a + b := by 
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num), h2, ha, hb, hc, sq_nonneg (a - b), sq_nonneg (a * b - c ^ 2), sq_nonneg (a * c - b * c), h₀, h₁, sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    
    linarith
  
  exact ⟨h5, h3⟩