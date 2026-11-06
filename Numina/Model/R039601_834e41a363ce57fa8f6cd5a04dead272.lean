import Mathlib

theorem algebra_189548 (x : ℝ) (hx : x > 0) :
    Real.sqrt (x ^ (Real.logb 10 (Real.sqrt x))) = 10 ↔ x = 100 ∨ x = 0.01 := by
  constructor
  · -- Assume Real.sqrt (x ^ (Real.logb 10 (Real.sqrt x))) = 10 prove x = 100 ∨ x = 0.01
    intro h
    have h1 : x ^ (Real.logb 10 (Real.sqrt x)) = 100 := by
      calc
        x ^ (Real.logb 10 (Real.sqrt x)) = (Real.sqrt (x ^ (Real.logb 10 (Real.sqrt x)))) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = 10 ^ 2 := by
          rw [h]
        _ = 100 := by
          norm_num
    have h2 : Real.logb 10 (Real.sqrt x) = (1 / 2) * Real.logb 10 x := by
      have h3 : Real.sqrt x = x ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h3]
      have h4 : Real.logb 10 (x ^ (1 / 2 : ℝ)) = (1 / 2) * Real.logb 10 x := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals linarith
      linarith [h4]
    have h3 : Real.logb 10 (x ^ (Real.logb 10 (Real.sqrt x))) = Real.logb 10 100 := by
      rw [h1]
    have h4 : Real.logb 10 (x ^ (Real.logb 10 (Real.sqrt x))) = Real.logb 10 (Real.sqrt x) * Real.logb 10 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h5 : Real.logb 10 (Real.sqrt x) * Real.logb 10 x = Real.logb 10 100 := by
      linarith [h4, h3]
    have h6 : Real.logb 10 100 = (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h6] at h5
    rw [show Real.logb 10 (Real.sqrt x) = (1 / 2) * Real.logb 10 x by linarith [h2]] at h5
    have h7 : (Real.logb 10 x) ^ 2 = 4 := by
      nlinarith
    have h8 : Real.logb 10 x = 2 ∨ Real.logb 10 x = -2 := by
      have h9 : (Real.logb 10 x - 2) * (Real.logb 10 x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- h10
        left
        linarith
      · -- h11
        right
        linarith
    cases h8 with
    | inl h9 =>
      have h10 : x = 100 := by
        have h11 : x = (10 : ℝ) ^ (Real.logb 10 x : ℝ) := by
          field_simp
        rw [show Real.logb 10 x = (2 : ℝ) by linarith [h9]] at h11
        norm_num at h11 ⊢
        linarith
      left
      linarith
    | inr h9 =>
      have h11 : x = (0.01 : ℝ) := by
        have h12 : x = (10 : ℝ) ^ (Real.logb 10 x : ℝ) := by
          field_simp
        rw [show Real.logb 10 x = (-2 : ℝ) by linarith [h9]] at h12
        norm_num at h12 ⊢
        linarith
      right
      linarith
  · -- Assume x = 100 or x = 0.01 prove Real.sqrt (x ^ (Real.logb 10 (Real.sqrt x))) = 10
    rintro (h | h)
    · -- x = 100
      rw [h]
      have h1 : Real.sqrt (100 : ℝ) = (10 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.logb 10 (Real.sqrt (100 : ℝ)) = (1 : ℝ) := by
        rw [h1]
        norm_num [Real.logb_eq_iff_rpow_eq]
      have h3 : (100 : ℝ) ^ (Real.logb 10 (Real.sqrt (100 : ℝ))) = (100 : ℝ) := by
        rw [h2]
        norm_num
      rw [h3]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    · -- x = 0.01
      rw [h]
      have h1 : Real.sqrt (0.01 : ℝ) = (0.1 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.logb 10 (Real.sqrt (0.01 : ℝ)) = (-1 : ℝ) := by
        rw [h1]
        norm_num [Real.logb_eq_iff_rpow_eq]
      have h3 : (0.01 : ℝ) ^ (Real.logb 10 (Real.sqrt (0.01 : ℝ))) = (100 : ℝ) := by
        rw [h2]
        norm_num
      rw [h3]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num