import Mathlib

theorem algebra_320607 (f : ℝ → ℝ) (hf : f = fun x => 3 * x ^ 3 + 2 * Real.sqrt 2 * x ^ 2 - (17 - 9 * Real.sqrt 2) * x - (6 - 5 * Real.sqrt 2)) :
    f (Real.sqrt 2 / 3) = 0 ∧ f (Real.sqrt 2 - 1) = 0 ∧ f (1 - 2 * Real.sqrt 2) = 0 := by
  have h1 : f (Real.sqrt 2 / 3) = 0 := by
    rw [hf]
    have h2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt 2) ^ 3 = (2 : ℝ) * (Real.sqrt 2) := by
      calc
        (Real.sqrt 2) ^ 3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2)^2 := by ring
        _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = (2 : ℝ) * (Real.sqrt 2 : ℝ) := by ring
    simp [h2, h3]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 2 - 1 : ℝ), sq_nonneg (1 - 2 * Real.sqrt 2 : ℝ), mul_pos (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)]
  have h4 : f (Real.sqrt 2 - 1) = 0 := by 
    rw [hf]
    have h5 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h6 : (Real.sqrt 2) ^ 3 = (2 : ℝ) * (Real.sqrt 2 : ℝ) := by
      calc
        (Real.sqrt 2) ^ 3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2)^2 := by ring
        _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        _ = (2 : ℝ) * (Real.sqrt 2 : ℝ) := by ring
    simp [h5, h6, pow_two]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 2 - 1 : ℝ), sq_nonneg (1 - 2 * Real.sqrt 2 : ℝ), mul_pos (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)]
  have h7 : f (1 - 2 * Real.sqrt 2) = 0 := by 
    rw [hf]
    have h8 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h9 : (Real.sqrt 2) ^ 3 = (2 : ℝ) * (Real.sqrt 2 : ℝ) := by
      calc
        (Real.sqrt 2) ^ 3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2)^2 := by ring
        _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        _ = (2 : ℝ) * (Real.sqrt 2 : ℝ) := by ring
    simp [h8, h9]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 2 - 1 : ℝ), sq_nonneg (1 - 2 * Real.sqrt 2 : ℝ), mul_pos (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)]
  exact ⟨h1, h4, h7⟩