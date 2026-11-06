import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_328000 {f : ℝ → ℝ} (hf : f = λ x => sqrt (1 - x)) :
    f 1 = 0 ∧ f 0 = 1 ∧ ∃ x y, x ≠ 1 ∧ y ≠ 1 ∧ f x = y ∧ f y = x ∧
      (x = (-1 + sqrt 5) / 2 ∧ y = (-1 + sqrt 5) / 2) := by 
  constructor 
  · -- Show that f(1) = 0 
    rw [hf]
    simp 
  constructor 
  · -- Show that f(0) = 1 
    rw [hf] 
    simp 
  · -- Show that there exists x and y such that x and y are not 1 
    use (-1 + sqrt 5) / 2, (-1 + sqrt 5) / 2
    constructor 
    · -- Show that x ≠ 1 
      by_contra h 
      have h1 : (-1 + sqrt 5) / 2 = (1 : ℝ) := by linarith [h] 
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    constructor 
    · -- Show that y ≠ 1 
      by_contra h 
      have h1 : (-1 + sqrt 5) / 2 = (1 : ℝ) := by linarith [h] 
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    constructor 
    · -- Show f x = y 
      rw [hf] 
      have h2 : (-1 + Real.sqrt 5) / 2 ≤ (1 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 1)]
      have h3 : sqrt (1 - (-1 + Real.sqrt 5) / 2) = (-1 + Real.sqrt 5) / 2 := by 
        have h6 : ((-1 + Real.sqrt 5) / 2) ^ 2 = 1 - (-1 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
        have h7 : (1 - (-1 + Real.sqrt 5) / 2 : ℝ) = ((-1 + Real.sqrt 5) / 2) ^ 2 := by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
        rw [h7] 
        have h8 : 0 ≤ (-1 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ)]
        have h9 : sqrt (((-1 + Real.sqrt 5) / 2) ^ 2) = (-1 + Real.sqrt 5) / 2 := by 
          rw [Real.sqrt_sq (show 0 ≤ (-1 + Real.sqrt 5) / 2 by nlinarith)]
        nlinarith 
      simp [h3]
    constructor 
    · -- Show f y = x 
      rw [hf] 
      have h4 : sqrt (1 - (-1 + Real.sqrt 5) / 2) = (-1 + Real.sqrt 5) / 2 := by 
        have h6 : ((-1 + Real.sqrt 5) / 2) ^ 2 = 1 - (-1 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
        have h7 : (1 - (-1 + Real.sqrt 5) / 2 : ℝ) = ((-1 + Real.sqrt 5) / 2) ^ 2 := by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
        rw [h7] 
        have h8 : 0 ≤ (-1 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ)]
        have h9 : sqrt (((-1 + Real.sqrt 5) / 2) ^ 2) = (-1 + Real.sqrt 5) / 2 := by 
          rw [Real.sqrt_sq (show 0 ≤ (-1 + Real.sqrt 5) / 2 by nlinarith)]
        nlinarith 
      simp [h4]
    · -- Show x = y 
      constructor 
      · -- Show x = (-1 + sqrt 5) / 2 
        ring
      · -- Show y = (-1 + sqrt 5) / 2 
        ring