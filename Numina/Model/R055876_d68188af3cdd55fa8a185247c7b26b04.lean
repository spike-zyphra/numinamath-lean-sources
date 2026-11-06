import Mathlib

open Real

theorem algebra_251842 {x : ℝ} (hx : 0 < x) (h : (x ^ logb 2 x - 1) ^ 2 = 1) :
    x = 1 / 2 ∨ x = 2 := by
  have eq1 : x ^ logb 2 x - 1 = 1 ∨ x ^ logb 2 x - 1 = -1 := by
    have h1 : (x ^ logb 2 x - 1) ^ 2 = 1 := h
    have : (x ^ logb 2 x - 1) ^ 2 - 1 = 0 := by linarith
    have : (x ^ logb 2 x - 1 - 1) * (x ^ logb 2 x - 1 + 1) = 0 := by
      ring_nf at this ⊢
      linarith
    cases' (mul_eq_zero.mp this) with h2 h3
    · left
      linarith
    · right
      linarith
  cases eq1 with
  | inl h2 =>
    have h3 : x ^ logb 2 x = 2 := by linarith
    have h4 : logb 2 (x ^ logb 2 x) = logb 2 2 := by
      rw [h3]
    have h5 : logb 2 (x ^ logb 2 x) = logb 2 x * logb 2 x := by
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try norm_num
        all_goals linarith
    rw [h5] at h4
    have h6 : logb 2 2 = 1 := by
      norm_num [logb_self_eq_one]
    rw [h6] at h4
    have h7 : (logb 2 x) ^ 2 = 1 := by nlinarith
    have h8 : logb 2 x = 1 ∨ logb 2 x = -1 := by
      have h9 : (logb 2 x - 1) * (logb 2 x + 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        left
        linarith
      | inr h11 =>
        right
        nlinarith
    cases h8 with
    | inl h9 =>
      have h10 : x = 2 := by
        have h11 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
          field_simp [hx.ne']
        rw [h11, h9]
        norm_num
      right
      exact h10
    | inr h9 =>
      have h10 : x = 1 / 2 := by
        have h11 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
          field_simp [hx.ne']
        rw [h11, h9]
        norm_num
      left
      exact h10
  | inr h2 =>
    have h3 : x ^ logb 2 x = 0 := by linarith
    have h4 : x ^ logb 2 x > 0 := by
      positivity
    linarith