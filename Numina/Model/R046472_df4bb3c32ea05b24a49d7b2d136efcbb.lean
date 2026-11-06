import Mathlib

open Real

theorem algebra_13491 {x : ℝ} (hx : 0 < x) :
    logb 4 (3 * x ^ 2 + 20) + logb 4 8 - 2 * logb 4 x = 3 ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2
    intro h_eq
    have h1 : 0 < 3 * x ^ 2 + 20 := by nlinarith
    have h2 : 0 < (x) := hx
    -- Use logarithm properties to combine the terms
    have h3 : logb 4 (3 * x ^ 2 + 20) + logb 4 8 = logb 4 ((3 * x ^ 2 + 20) * 8) := by
      rw [← logb_mul (by positivity) (by positivity)]
    -- The term 2 * logb 4 x can be rewritten as logb 4 (x ^ 2)
    have h4 : 2 * logb 4 x = logb 4 (x ^ 2) := by
      simp [logb_pow]
    -- Rewrite the equation using these properties
    have h5 : logb 4 (3 * x ^ 2 + 20) + logb 4 8 - 2 * logb 4 x = logb 4 ((3 * x ^ 2 + 20) * 8) - logb 4 (x ^ 2) := by
      linarith [h3, h4]
    rw [h5] at h_eq
    have h6 : logb 4 ((3 * x ^ 2 + 20) * 8) - logb 4 (x ^ 2) = logb 4 (( (3 * x ^ 2 + 20) * 8 ) / (x ^ 2)) := by
      field_simp [logb_div]
    rw [h6] at h_eq
    -- Convert the logarithmic equation to its exponential form
    have h7 : ( (3 * x ^ 2 + 20) * 8 ) / (x ^ 2) = (4: ℝ) ^ 3 := by
      have h8 : logb 4 (( (3 * x ^ 2 + 20) * 8 ) / (x ^ 2)) = 3 := h_eq
      have h9 : ( (3 * x ^ 2 + 20) * 8 ) / (x ^ 2) = (4: ℝ) ^ 3 := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by
          have h4_pos : 0 < (4: ℝ) := by norm_num
          have hx2_pos : 0 < x ^ 2 := by nlinarith
          have h3_pos : 0 < ( (3 * x ^ 2 + 20) * 8 ) / x ^ 2 := by
            apply div_pos
            all_goals nlinarith
          linarith
        )] at h8
        · nlinarith
        all_goals nlinarith
      exact h9
    -- Simplify the results to find x
    have h8 : ( (3 * x ^ 2 + 20) * 8 ) / (x ^ 2) = (64: ℝ) := by
      rw [h7]
      norm_num
    have h9 : ( (3 * x ^ 2 + 20) * 8 ) = (64: ℝ) * (x ^ 2) := by
      have h10 : ( (3 * x ^ 2 + 20) * 8 ) / x ^ 2 = (64: ℝ) := by
        linarith [h8]
      have h11 : x ^ 2 > 0 := by nlinarith
      have h12 : ( (3 * x ^ 2 + 20) * 8 ) = (64: ℝ) * (x ^ 2) := by
        field_simp at h10 ⊢
        nlinarith
      exact h12
    have h10 : x ^ 2 = (4: ℝ) := by
      nlinarith
    have h11 : x = 2 := by
      nlinarith [h10, hx]
    exact h11
  · -- Assume x = 2, prove the equation holds
    intro h_eq
    rw [h_eq]
    have h1 : 0 < (3: ℝ) * (2: ℝ) ^ 2 + 20 := by norm_num
    have h2 : 0 < (2: ℝ) := by norm_num
    -- Verify the equation holds by direct calculation
    have h3 : logb 4 (3 * (2: ℝ) ^ 2 + 20) + logb 4 8 - 2 * logb 4 (2: ℝ) = 3 := by
      have h4 : logb 4 (3 * (2: ℝ) ^ 2 + 20) + logb 4 8 = logb 4 ((3 * (2: ℝ) ^ 2 + 20) * 8) := by
        rw [← logb_mul (by positivity) (by positivity)]
      have h5 : 2 * logb 4 (2: ℝ) = logb 4 ((2: ℝ) ^ 2) := by
        simp [logb_pow]
      have h8 : (3 * (2: ℝ) ^ 2 + 20) * 8 = (256: ℝ) := by norm_num
      have h9 : logb 4 ((3 * (2: ℝ) ^ 2 + 20) * 8) = (4: ℝ) := by
        rw [h8]
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)] <;> norm_num
      have h10 : logb 4 ((2: ℝ) ^ 2) = (1: ℝ) := by
        have h32 : (2: ℝ) ^ 2 = (4: ℝ) := by norm_num
        rw [h32]
        have h44 : logb (4: ℝ) (4: ℝ) = (1: ℝ) := by
          rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)] <;> norm_num
        linarith [h44]
      linarith [h4, h5, h9, h10]
    linarith [h3]