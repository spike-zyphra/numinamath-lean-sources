import Mathlib

open Real
open scoped BigOperators

theorem inequalities_324949 (k : ℝ) :
  (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a^2 + b^2 = c^2 → a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ k * a * b * c) ↔
  k ≤ 2 + 3 * sqrt 2 := by
  constructor
  · -- First, prove the maximum value of k is 2 + 3 * sqrt 2
    intro h
    have h1 := h 1 1 (Real.sqrt 2) (show (1 : ℝ) > 0 by norm_num) (show (1 : ℝ) > 0 by norm_num) (show Real.sqrt 2 > 0 by positivity) (show (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 by
      have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith
    )
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : (1 : ℝ) ^ 2 * (1 + Real.sqrt 2) + (1 : ℝ) ^ 2 * (Real.sqrt 2 + 1) + (Real.sqrt 2) ^ 2 * (1 + 1) ≥ k * (1 : ℝ) * (1 : ℝ) * (Real.sqrt 2) := by
      linarith [h1, h2]
    have h4 : (1 : ℝ) ^ 2 * (1 + Real.sqrt 2) + (1 : ℝ) ^ 2 * (Real.sqrt 2 + 1) + (Real.sqrt 2) ^ 2 * (1 + 1) = 6 + 2 * Real.sqrt 2 := by
      nlinarith [h2]
    have h5 : k * (1 : ℝ) * (1 : ℝ) * (Real.sqrt 2) ≤ 6 + 2 * Real.sqrt 2 := by
      linarith [h3, h4]
    have h6 : Real.sqrt 2 > 0 := by positivity
    have h7 : k ≤ (6 + 2 * Real.sqrt 2) / (Real.sqrt 2) := by
      have h6' : Real.sqrt 2 > 0 := h6
      apply (le_div_iff₀ h6').mpr
      linarith [h5]
    have h8 : (6 + 2 * Real.sqrt 2) / (Real.sqrt 2) = 2 + 3 * Real.sqrt 2 := by 
      field_simp [h6]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith [h7, h8]
  · -- Now, we need to prove the inequality holds if k ≤ 2 + 3 * sqrt 2
    rintro hk 
    intro a b c ha hb hc h1 
    have h4 : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ (2 + 3 * Real.sqrt 2) * a * b * c := by 
      have h51 : c ^ 2 = a^2 + b^2 := by linarith
      have h54 : Real.sqrt 2 > 0 := by positivity
      have h55 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h56 : Real.sqrt 2 ^ 4 = 4 := by 
        calc
          Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring 
          _ = 2 ^ 2 := by rw [h55]
          _ = 4 := by norm_num
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (c - a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg ((a - b)), sq_nonneg ((a + b - c)), 
        sq_nonneg ((a * c) - (b * c)), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
        sq_nonneg ((a) - (b)), sq_nonneg ((a) * (Real.sqrt 2) - (b) * (Real.sqrt 2)), sq_nonneg ((c) - (Real.sqrt 2) * (a)), sq_nonneg ((c) - (Real.sqrt 2) * (b)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, Real.sqrt_nonneg 2, 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
        sq_nonneg (a^2 - b^2), sq_nonneg (a * b - b * c), sq_nonneg (a * c - a * b), 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < a * b * c by positivity)
      ]
    have h9 : k ≤ (2 + 3 * Real.sqrt 2) := hk 
    have h22 : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ k * a * b * c := by 
      have eq1 : k * a * b * c ≤ (2 + 3 * Real.sqrt 2) * a * b * c := by 
        have eq2 : k ≤ (2 + 3 * Real.sqrt 2) := h9 
        have pos1 : a * b * c > 0 := by 
          positivity 
        nlinarith [eq2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      linarith [h4, eq1] 
    linarith [h22]