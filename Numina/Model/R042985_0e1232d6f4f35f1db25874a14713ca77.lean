import Mathlib
open Real
theorem algebra_174457 (x : ℝ) (hx : -x ^ 2 + x + 2 ≥ 0): √(-x ^ 2 + x + 2) * (sin (2 * x) - π * cos x) = 0 ↔ x = -1 ∨ x = 2 ∨ x = π / 2:= by
  constructor
  · -- ⇒: if the equation holds, then x ∈ {-1, 2, π/2}
    intro h
    have h1 : √(-x ^ 2 + x + 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : √(-x ^ 2 + x + 2) = 0 ∨ sin (2 * x) - π * cos x = 0 := by 
      cases (mul_eq_zero.1 h) with
      | inl h4 =>
        left
        linarith [h4]
      | inr h4 =>
        right
        linarith [h4]
    rcases h3 with h3 | h3
    · -- √(-x^2 + x + 2) = 0 
      have h4 : -x ^ 2 + x + 2 = 0 := by
        have h5 : √(-x ^ 2 + x + 2) = 0 := h3
        rw [Real.sqrt_eq_zero (by linarith)] at h5 
        linarith
      have h5 : x ^ 2 - x - 2 = 0 := by
        nlinarith
      have h6 : (x - 2) * (x + 1) = 0 := by nlinarith 
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- x - 2 = 0, so x = 2 
        right 
        left 
        linarith 
      · -- x + 1 = 0, so x = -1 
        left 
        linarith
    · -- sin (2 * x) - π * cos x = 0
      have h4 : sin (2 * x) = π * cos x := by
        linarith 
      have h5 : sin (2 * x) = 2 * sin x * cos x := by 
        rw [sin_two_mul]
      rw [h5] at h4 
      have h6 : cos x * (2 * sin x - π) = 0 := by
        linarith 
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- cos x = 0 
        have h8 : cos x = 0 := by 
          linarith 
        have h9 : x = π / 2 := by
          have h40 : cos x = 0 := h8
          have h11 : x ≥ -1 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2), hx]
          have h12 : x ≤ 2 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2), hx]
          by_cases h14 : x < (π / 2 : ℝ)
          · -- Assume x < π / 2 
            have h15 : cos x > 0 := by
              apply cos_pos_of_mem_Ioo 
              constructor
              · nlinarith [Real.pi_pos, h14, Real.pi_gt_three]
              · nlinarith [Real.pi_pos, h14, Real.pi_gt_three]
            nlinarith 
          by_cases h16 : x > (π / 2 : ℝ)
          · -- Assume x > π / 2 
            have h16 : x ≤ 2 := by nlinarith 
            have h17 : cos x < 0 := by 
              apply cos_neg_of_pi_div_two_lt_of_lt 
              all_goals linarith [Real.pi_pos, h16, h16, Real.pi_gt_three] 
            nlinarith 
          linarith 
        right 
        right 
        exact h9 
      · -- 2 * sin x - π = 0 
        nlinarith [Real.pi_gt_three, Real.sin_le_one x, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq x]
  · -- ⇐: if x ∈ {-1, 2, π/2}, then the equation holds 
    rintro (h | h | h)
    · -- x = -1 
      rw [h]
      have h1 : -(-1: ℝ) ^ 2 + (-1: ℝ) + 2 = 0 := by
        nlinarith 
      have h11 : √(-(-1: ℝ) ^ 2 + (-1: ℝ) + 2) = 0 := by
        rw [h1] 
        simp 
      rw [h11] 
      norm_num 
    · -- x = 2 
      rw [h]
      have h1 : -(2: ℝ) ^ 2 + (2: ℝ) + 2 = 0 := by
        nlinarith 
      have h3 : √(-(2: ℝ) ^ 2 + (2: ℝ) + 2) = 0 := by 
        rw [h1] 
        simp 
      rw [h3] 
      norm_num 
    · -- x = π / 2 
      rw [h]
      have h4 : sin (2 * (π / 2 : ℝ)) = π * cos (π / 2 : ℝ) := by 
        have h5 : sin (2 * (π / 2 : ℝ)) = 0 := by
          have h10 : 2 * (π / 2 : ℝ) = π := by
            ring 
          rw [h10]
          simp [sin_pi]
        have h6 : cos (π / 2 : ℝ) = 0 := by 
          exact cos_pi_div_two 
        rw [h5, h6] 
        <;> nlinarith 
      have h9 : sin (2 * (π / 2 : ℝ)) - π * cos (π / 2 : ℝ) = 0 := by 
        linarith [h4] 
      rw [h9] 
      norm_num