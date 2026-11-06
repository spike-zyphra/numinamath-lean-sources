import Mathlib

open Real
theorem number_theory_459682 (h : ∃d, √3 = √5 - d ∧ √5 = √7 - d) :
    False := by
  rcases h with ⟨d, h1, h2⟩
  have h3 : d = √5 - √3 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (3: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7: ℝ) by norm_num)]
  have h4 : d = √7 - √5 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (3: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7: ℝ) by norm_num)]
  have h5 : √5 - √3 = √7 - √5 := by
    linarith [h3, h4]
  have h6 : 2 * √5 = √3 + √7 := by
    nlinarith [h5, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 7]
  have h7 : (2 * √5) ^2 = (√3 + √7) ^2 := by 
    rw [h6]
  have h8 : (2 * √5) ^2 = 20 := by
    calc
      (2 * √5) ^2 = 4 * (√5 ^2) := by ring
      _ = 4 * 5 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      _ = 20 := by norm_num
  have h9 : (√3 + √7) ^2 = 10 + 2 * (√3 * √7) := by
    calc
      (√3 + √7) ^2 = (√3) ^2 + (√7) ^2 + 2 * (√3 * √7) := by ring
      _ = 3 + 7 + 2 * (√3 * √7) := by 
        have h3sq : (√3) ^2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (3 : ℝ))
        have h7sq : (√7) ^2 = 7 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (7 : ℝ))
        rw [h3sq, h7sq]
      _ = 10 + 2 * (√3 * √7) := by ring
  have h10 : (√3 * √7) = Real.sqrt 21 := by 
    have h11 : √3 * √7 = √(3 * 7 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h11]
    all_goals norm_num
  have h11 : 20 = 10 + 2 * Real.sqrt 21 := by
    nlinarith [h7, h8, h9, h10, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 7]
  have h12 : 5 = Real.sqrt 21 := by 
    nlinarith [h11, Real.sqrt_nonneg 21]
  have h13 : (5 : ℝ) ^2 = (Real.sqrt 21) ^2 := by
    rw [h12]
  have h14 : (5 : ℝ) ^2 = (25 : ℝ) := by norm_num
  have h15 : (Real.sqrt 21) ^2 = (21 : ℝ) := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  nlinarith [h13, h14, h15, Real.sqrt_nonneg 21]