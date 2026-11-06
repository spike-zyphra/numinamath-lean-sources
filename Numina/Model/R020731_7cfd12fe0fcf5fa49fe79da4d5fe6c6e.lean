import Mathlib

open Real

theorem algebra_167165 {x : ℝ} (hx : x > 0) (hx1 : x ≠ 1) :
    sqrt (3 * (logb 2 x)^2 - 1 - 9 * (logb x 2)^2) = 5 ↔
    x = 1 / 8 ∨ x = 8 := by
  constructor
  · -- Forward: if $\sqrt{3 \log _{2}^{2 27-1- 9 \log _{x}^{2 2} 2}=5$, then $x = \frac{1}{8}$ or $x = 8$.
    intro h_eq
    have h1 : 0 ≤ (3 * (logb 2 x)^2 - 1 - 9 * (logb x 2)^2 : ℝ) := by
      by_contra h
      push_neg at h
      have h2 : sqrt (3 * (logb 2 x)^2 - 1 - 9 * (logb x 2)^2) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
      rw [h2] at h_eq
      nlinarith
    have h_eq1 : (3 * (logb 2 x)^2 - 1 - 9 * (logb x 2)^2 : ℝ) = 25 := by
      calc
        (3 * (logb 2 x)^2 - 1 - 9 * (logb x 2)^2 : ℝ) = (sqrt (3 * (logb 2 x)^2 - 1 - 9 * (logb x 2)^2) ) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith [h1]
        _ = (5 : ℝ) ^ 2 := by
          rw [h_eq]
        _ = (25 : ℝ) := by
          norm_num
    have h2 : logb x 2 = 1 / (logb 2 x) := by
      field_simp [logb]
    rw [h2] at h_eq1
    have h3 : logb 2 x ≠ 0 := by
      by_contra h
      have h4 : logb 2 x = 0 := by
        linarith
      have h5 : x = 1 := by
        have h6 : logb 2 x = 0 := h4
        rw [logb_eq_iff_rpow_eq] at h6
        · -- Show that $x = 1$
          have : x = (2 : ℝ) ^ (0 : ℝ) := by linarith [h6]
          rw [show (2 : ℝ) ^ (0 : ℝ) = 1 by norm_num] at this
          linarith
        all_goals
          all_goals linarith
      contradiction
    have h_eq2 : 3 * (logb 2 x) ^ 4 - 26 * (logb 2 x) ^ 2 - 9 = 0 := by
      field_simp [(show logb 2 x ≠ 0 from h3), pow_two] at h_eq1 ⊢
      nlinarith [sq_pos_of_ne_zero (show logb 2 x ≠ 0 by exact h3)]
    have h_eq3 : (logb 2 x) ^ 2 = 9 := by
      have h_eq5 : 3 * ((logb 2 x) ^ 2) ^ 2 - 26 * (logb 2 x) ^ 2 - 9 = 0 := by
        nlinarith
      have h_eq6 : ((logb 2 x) ^ 2 - 9) * ((logb 2 x) ^ 2 + 1 / 3) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h_eq6) with
      | inl h_eq7 =>
        linarith
      | inr h_eq8 =>
        nlinarith [sq_nonneg (logb 2 x)]
    have h_eq4 : logb 2 x = 3 ∨ logb 2 x = -3 := by
      have h_eq6 : (logb 2 x) ^ 2 = 9 := h_eq3
      have : logb 2 x = 3 ∨ logb 2 x = -3 := by
        have h_eq7 : (logb 2 x) ^ 2 - 9 = 0 := by
          nlinarith
        have h_eq8 : (logb 2 x - 3) * (logb 2 x + 3) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h_eq8) with
        | inl h_eq9 =>
          left
          linarith
        | inr h_eq10 =>
          right
          nlinarith
      assumption
    cases h_eq4 with
    | inl h_eq6 =>
      have h_eq7 : x = (2 : ℝ)  ^ (3 : ℝ) := by
        have h_eq8 : logb 2 x = 3 := h_eq6
        rw [logb_eq_iff_rpow_eq] at h_eq8
        · -- Show that $x = 2^3$
          linarith
        all_goals
          all_goals linarith
      have h_eq8 : x = 8 := by
        norm_num at h_eq7 ⊢
        linarith
      right
      tauto
    | inr h_eq9 =>
      have h_eq10 : x = (2 : ℝ) ^ (-3 : ℝ) := by
        have h_eq8 : logb 2 x = -3 := h_eq9
        rw [logb_eq_iff_rpow_eq] at h_eq8
        · -- Show that $x = 2^{-3} 8$
          linarith
        all_goals
          all_goals linarith
      have h_eq11 : x = 1 / 8 := by
        norm_num at h_eq10 ⊢
        linarith
      left
      tauto
  · -- Backward implication: if $x = \frac{1}{8}$ or $x = 8$, then $\sqrt{3 \log _{2}^{2} 8-1- 9 \log _{8}^{2} 2}=5$.
    rintro (h_eq | h_eq)
    · -- Case $x = 1/8$
      rw [h_eq]
      have h1 : logb 2 (1 / 8 : ℝ) = -3 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h2 : logb (1 / 8 : ℝ) (2 : ℝ) = -1 / 3 := by
        have h1' : logb (1 / 8 : ℝ) (2 : ℝ) = (logb 2 (2 : ℝ)) / (logb 2 (1 / 8 : ℝ)) := by
          field_simp [logb]
        rw [h1']
        have h4 : logb 2 (2 : ℝ) = 1 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h4, h1]
        all_goals norm_num
      have h3 : (3 * (logb 2 (1 / 8 : ℝ)) ^ 2 - 1 - 9 * (logb (1 / 8 : ℝ) (2 : ℝ)) ^ 2 : ℝ) = (25 : ℝ) := by
        rw [h1, h2]
        norm_num
      rw [h3]
      exact Real.sqrt_eq_cases.2 (by norm_num)
    · -- Case $x = 8$
      rw [h_eq]
      have h1 : logb 2 (8 : ℝ) = 3 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h2 : logb (8 : ℝ) (2 : ℝ) = 1 / 3 := by
        have h1' : logb (8 : ℝ) (2 : ℝ) = (logb 2 (2 : ℝ)) / (logb 2 (8 : ℝ)) := by
          field_simp [logb]
        rw [h1']
        have h4 : logb 2 (2 : ℝ) = 1 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h4, h1]
        all_goals norm_num
      have h3 : (3 * (logb 2 (8 : ℝ)) ^ 2 - 1 - 9 * (logb (8 : ℝ) (2 : ℝ)) ^ 2 : ℝ) = (25 : ℝ) := by
        rw [h1, h2]
        norm_num
      rw [h3]
      exact Real.sqrt_eq_cases.2 (by norm_num)