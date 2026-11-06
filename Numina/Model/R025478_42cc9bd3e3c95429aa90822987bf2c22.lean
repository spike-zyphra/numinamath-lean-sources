import Mathlib

theorem algebra_167006 (x : ℝ) (hx : x > 0) :
    3^(Real.logb 3 x)^2 + x^(Real.logb 3 x) = 162 ↔ x = 1 / 9 ∨ x = 9 := by
  constructor
  · -- Assume the equation holds, prove x = 1/9 or x = 9
    intro h_eq
    have h1 : x ^ (Real.logb 3 x) = (3 : ℝ) ^ ((Real.logb 3 x) ^ 2) := by
      have h3 : (3 : ℝ) ^ (Real.logb 3 x) = x := by 
        field_simp [Real.rpow_logb, hx, show (3 : ℝ) > 1 by norm_num]
      calc
        x ^ (Real.logb 3 x) = ((3 : ℝ) ^ (Real.logb 3 x)) ^ (Real.logb 3 x) := by 
          rw [show (3 : ℝ) ^ (Real.logb 3 x) = x by
            field_simp [Real.rpow_logb, hx, show (3 : ℝ) > 1 by norm_num]
          ]
        _ = (3 : ℝ) ^ (Real.logb 3 x * Real.logb 3 x) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals linarith
        _ = (3 : ℝ) ^ ((Real.logb 3 x) ^ 2) := by
          ring_nf
    rw [h1] at h_eq
    have h2 : (3 : ℝ) ^ ((Real.logb 3 x) ^ 2) = 81 := by
      nlinarith
    have h3 : (Real.logb 3 x) ^ 2 = (4 : ℝ) := by
      have h4 : (3 : ℝ) ^ ((Real.logb 3 x) ^ 2) = 81 := h2
      have h5 : (3 : ℝ) ^ (4 : ℝ) = (81 : ℝ) := by norm_num
      rw [← h5] at h4
      have h6 : (Real.logb 3 x) ^ 2 = (4 : ℝ) := by
        apply_fun (Real.logb (3 : ℝ)) at h4
        simp at h4 ⊢
        nlinarith
      linarith
    have h4 : Real.logb 3 x = 2 ∨ Real.logb 3 x = -2 := by
      have h5 : (Real.logb 3 x) ^ 2 = (4 : ℝ) := h3
      have h6 : (Real.logb 3 x - 2) * (Real.logb 3 x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case h7: Real.logb 3 x - 2 = 0
        left
        linarith
      · -- Case h8: Real.logb 3 x + 2 = 0
        right
        linarith
    cases h4 with
    | inl h5 =>
      -- If Real.logb 3 x = 2, then x = 3^2 = 9
      have h6 : x = (9 : ℝ) := by
        have h7 : Real.logb 3 x = (2 : ℝ) := h5
        have h8 : x = (3 : ℝ) ^ (Real.logb 3 x) := by
          field_simp [Real.rpow_logb, hx, show (3 : ℝ) > 1 by norm_num]
        rw [h7] at h8
        norm_num at h8 ⊢
        linarith
      right
      linarith
    | inr h5 =>
      -- If Real.logb 3 x = -2, then x = 3^(-2) = 1/9
      have h6 : x = (1 / 9 : ℝ) := by
        have h7 : Real.logb 3 x = (-2 : ℝ) := h5
        have h8 : x = (3 : ℝ) ^ (Real.logb 3 x) := by
          field_simp [Real.rpow_logb, hx, show (3 : ℝ) > 1 by norm_num]
        rw [h7] at h8
        norm_num at h8 ⊢
        linarith
      left
      linarith
  · -- Backward implication: if x is 1/9 or 9, then the equation holds
    rintro (h_eq | h_eq)
    · -- Case x = 1/9
      rw [h_eq]
      have h1 : Real.logb (3 : ℝ) (1 / 9 : ℝ) = -2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- Case x = 9
      rw [h_eq]
      have h1 : Real.logb (3 : ℝ) (9 : ℝ) = (2 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h1]
      norm_num