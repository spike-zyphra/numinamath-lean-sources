import Mathlib

open Real

theorem algebra_601033 {x : ℝ} (hx : x > 0) (hx1 : x ≠ 1) :
    logb 3 x + logb x 3 - 2 * logb 3 x * logb x 3 = 1 / 2 ↔ x = sqrt 3 ∨ x = 9 := by
  constructor
  · -- Assume the equation holds, prove $x = \sqrt{3}$ or $x = 9$
    intro h_eq
    have h1 : logb x 3 = 1 / logb 3 x := by
      field_simp [logb]
    rw [h1] at h_eq
    have h2 : logb 3 x ≠ 0 := by
      by_contra h3
      have h4 : logb 3 x = 0 := by linarith
      have h5 : x = 1 := by
        rw [logb_eq_iff_rpow_eq] at h4
        · -- Show x = 1 if logb 3 x = 0
          linarith
        all_goals
          try linarith
          try tauto
      contradiction
    have eq2 : logb 3 x + 1 / logb 3 x = 5 / 2 := by
      have h6 : logb 3 x * (1 / logb 3 x) = 1 := by 
        field_simp [h2]
      nlinarith [h_eq, h6]
    have eq3 : 2 * (logb 3 x) ^ 2 - 5 * logb 3 x + 2 = 0 := by
      have h7 : logb 3 x ≠ 0 := h2
      have eq4 : logb 3 x + 1 / logb 3 x = 5 / 2 := eq2
      field_simp [h7] at eq4
      nlinarith [eq4]
    have h8 : (logb 3 x - 2) * (2 * logb 3 x - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- $\log_3 x - 2 = 0$
      have eq4 : logb 3 x = 2 := by linarith
      have eq5 : x = (3 : ℝ) ^ (2 : ℝ) := by 
        rw [logb_eq_iff_rpow_eq] at eq4
        · -- Show x = 3 ^ (2 : ℝ) if $\log_3 x = 2$
          linarith
        all_goals
          try linarith
          try tauto
      have eq5' : x = (9 : ℝ) := by
        norm_num at eq5 ⊢
        try linarith
      right
      linarith
    · -- $2 \cdot \log_3 x - 1 = 0$
      have eq7 : logb 3 x = 1 / 2 := by linarith
      have eq8 : x = (3 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [logb_eq_iff_rpow_eq] at eq7
        · -- Show x = 3 ^ (1 / 2 : ℝ) if $\log_3 x = 1 / 2$
          linarith
        all_goals
          try linarith
          try tauto
      have eq9 : x = Real.sqrt 3 := by
        have h11 : x = (3 : ℝ) ^ (1 / 2 : ℝ) := eq8
        have h12 : (3 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 3 := by
          rw [Real.sqrt_eq_rpow]
        rw [h12] at h11
        linarith
      left
      linarith
  · -- Assume $x = \sqrt{3}$ or $x = 9$, prove the equation
    rintro (h_eq | h_eq)
    · -- x = Real.sqrt 3
      rw [h_eq]
      have h1 : logb 3 (Real.sqrt 3) = 1 / 2 := by 
        rw [Real.sqrt_eq_rpow]
        rw [logb_rpow]
        all_goals
          norm_num
      have h2 : logb (Real.sqrt 3) (3 : ℝ) = 2 := by
        rw [logb]
        have h3 : log (Real.sqrt 3) = (1 / 2) * log (3 : ℝ) := by
          calc 
            log (Real.sqrt 3) = log ((3 : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [Real.sqrt_eq_rpow]
            _ = (1 / 2 : ℝ) * log (3 : ℝ) := by
              rw [log_rpow]
              all_goals
                norm_num
        field_simp [h3]
        <;> nlinarith
      rw [h1, h2]
      norm_num
    · -- x = 9
      rw [h_eq]
      have h1 : logb 3 (9 : ℝ) = 2 := by 
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h2 : logb (9 : ℝ) (3 : ℝ) = 1 / 2 := by
        rw [logb]
        have h4 : log (3 : ℝ) = log (3 : ℝ) := by
          rfl
        have h5 : log (9 : ℝ) = 2 * log (3 : ℝ) := by
          calc 
            log (9 : ℝ) = log ((3 : ℝ) ^ 2) := by
              norm_num
            _ = 2 * log (3 : ℝ) := by
              simp [log_pow]
        field_simp [h4, h5]
        <;> nlinarith
      rw [h1, h2]
      norm_num