import Mathlib

theorem algebra_21473 {d : Set ℝ} (hd : d = {x : ℝ | x ^ 2 - 2 * x + 2 ≥ 0 ∧ -x ^ 2 + 6 * x - 2 ≥ 0 ∧ x ≥ 0}) :
    IsLeast {x : ℝ | x ∈ d ∧ Real.sqrt (x ^ 2 - 2 * x + 2) + Real.sqrt (-x ^ 2 + 6 * x - 2) = 2 * Real.sqrt x} (3 - Real.sqrt 7) := by 
  have h1 : (3 - Real.sqrt 7 : ℝ) ^ 2 - 2 * (3 - Real.sqrt 7) + 2 ≥ 0 := by 
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  have h2 : -(3 - Real.sqrt 7 : ℝ) ^ 2 + 6 * (3 - Real.sqrt 7 : ℝ) - 2 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  have h3 : (3 - Real.sqrt 7 : ℝ) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  have h4 : (3 - Real.sqrt 7) ∈ d := by
    rw [hd]
    exact ⟨by nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)], by nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)], by nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]⟩
  have h5 : Real.sqrt ((3 - Real.sqrt 7) ^ 2 - 2 * (3 - Real.sqrt 7) + 2) + Real.sqrt (-(3 - Real.sqrt 7) ^ 2 + 6 * (3 - Real.sqrt 7) - 2) = 2 * Real.sqrt (3 - Real.sqrt 7) := by 
    have h6 : Real.sqrt (-(3 - Real.sqrt 7 ) ^ 2 + 6 * (3 - Real.sqrt 7 ) - 2) = 0 := by 
      have h7 : (-(3 - Real.sqrt 7 ) ^ 2 + 6 * (3 - Real.sqrt 7 ) - 2 : ℝ) = 0 := by 
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      rw [h7]
      simp 
    rw [h6]
    have h8 : Real.sqrt ((3 - Real.sqrt 7 : ℝ) ^ 2 - 2 * (3 - Real.sqrt 7 : ℝ) + 2) = 2 * Real.sqrt (3 - Real.sqrt 7) := by 
      have h9 : ( (3 - Real.sqrt 7 : ℝ) ^ 2 - 2 * (3 - Real.sqrt 7 : ℝ) + 2 ) = (2 * Real.sqrt (3 - Real.sqrt 7)) ^ 2 := by
        have h10 : ( (3 - Real.sqrt 7 : ℝ) ^ 2 - 2 * (3 - Real.sqrt 7 : ℝ) + 2 ) = (12 - 4 * Real.sqrt 7) := by 
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
        have h11 : (2 * Real.sqrt (3 - Real.sqrt 7)) ^ 2 = (12 - 4 * Real.sqrt 7) := by
          calc
            (2 * Real.sqrt (3 - Real.sqrt 7)) ^ 2 = 4 * (Real.sqrt (3 - Real.sqrt 7)) ^ 2 := by ring
            _ = 4 * (3 - Real.sqrt 7) := by
              rw [Real.sq_sqrt]
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            _ = (12 - 4 * Real.sqrt 7) := by
              nlinarith 
        rw [h10, h11]
      have h12 : Real.sqrt ((3 - Real.sqrt 7 : ℝ) ^ 2 - 2 * (3 - Real.sqrt 7 : ℝ) + 2) = Real.sqrt ( (2 * Real.sqrt (3 - Real.sqrt 7 : ℝ) ) ^ 2 ) := by
        rw [h9]
      have h13 : Real.sqrt ( (2 * Real.sqrt (3 - Real.sqrt 7 : ℝ) ) ^ 2 ) = (2 * Real.sqrt (3 - Real.sqrt 7 : ℝ) ) := by 
        rw [Real.sqrt_sq (show 0 ≤ (2 * Real.sqrt (3 - Real.sqrt 7 : ℝ) ) by positivity)]
      rw [h12, h13]
    nlinarith [Real.sqrt_nonneg (12 - 4 * Real.sqrt 7), Real.sqrt_nonneg (3 - Real.sqrt 7)]
  constructor 
  · -- Show 3 - sqrt 7 is in the set 
    constructor 
    · -- Show x ∈ d 
      exact h4
    · -- Show equation 
      exact h5 
  · -- Show it is the least
    intro x hx 
    rcases hx with ⟨hx1, hx2⟩ 
    rw [hd] at hx1 
    rcases hx1 with ⟨h1, h2, h3⟩ 
    by_contra h 
    push_neg at h 
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 2 * x + 2), Real.sqrt_nonneg (-x ^ 2 + 6 * x - 2), Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 2 * x + 2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ -x ^ 2 + 6 * x - 2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num : (7 : ℝ) > 0) ]