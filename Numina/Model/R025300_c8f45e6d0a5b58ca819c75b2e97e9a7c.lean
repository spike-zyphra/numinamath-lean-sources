import Mathlib

open Real

theorem algebra_187990 {x : ℝ} (hx : 0 < x ∧ x ≠ 1) :
    2 * logb x 27 - 3 * logb 27 x = 1 ↔ x = 1 / 27 ∨ x = 9 := by

  constructor
  · -- Assume 2 * logb x 27 - 3 * logb 27 x = 1, prove x = 1 / 27 ∨ x = 9
    intro h_eq
    have hx1 : 0 < x := hx.1
    have hx2 : x ≠ 1 := hx.2

    have h1 : 2 * logb x 27 - 3 * logb 27 x = 2 * (log 27 / log x) - 3 * (log x / log 27) := by
      have h2 : logb x 27 = log 27 / log x := by
        field_simp [logb]
      have h3 : logb 27 x = log x / log 27 := by
        field_simp [logb]
      rw [h2, h3]

    rw [h1] at h_eq

    have h2 : log 27 > 0 := by
      apply log_pos
      all_goals norm_num

    have h3 : log x ≠ 0 := by
      by_contra h4
      have h5 : x = 1 := by
        have h6 : log x = 0 := h4
        rw [log_eq_zero] at h6
        rcases h6 with (r | r | r)
        · linarith
        · linarith
        · linarith
      tauto

    have h4 : 2 * (log 27) ^ 2 - (log x) * (log 27) - 3 * (log x) ^ 2 = 0 := by
      have h5 : log x ≠ 0 := h3
      have h6 : log 27 > 0 := h2
      field_simp [h5, h2] at h_eq ⊢
      nlinarith [h_eq]

    have h5 : (log x + log 27) * (log x - (2 / 3) * log 27) = 0 := by
      nlinarith [h4]

    cases' (mul_eq_zero.mp h5) with h6 h7

    · -- Case 1: h6 : log x + log 27 = 0
      have h8 : log x = -log 27 := by
        linarith

      have h9 : log (x * 27) = 0 := by
        have h10 : log (x * 27) = log x + log 27 := by
          rw [log_mul (by linarith) (by linarith)]
        linarith [h10, h8]

      have h10 : x * 27 = 1 := by
        have h11 : x * 27 > 0 := by
          nlinarith
        have h12 : x * 27 = Real.exp (log (x * 27)) := by
          rw [Real.exp_log]
          all_goals nlinarith
        rw [h9] at h12
        have h13 : Real.exp (0 : ℝ) = 1 := Real.exp_zero
        rw [h13] at h12
        linarith

      have h11 : x = 1 / 27 := by
        nlinarith

      left
      exact h11

    · -- Case 2: h7 : log x - (2 / 3) * log 27 = 0
      have h12 : log x = (2 / 3) * log 27 := by
        linarith [h7]

      have h13 : log 27 = 3 * log 3 := by
        calc
          log 27 = log (3 ^ 3) := by norm_num
          _ = 3 * log 3 := by simp [log_pow]

      have h14 : log x = 2 * log 3 := by
        rw [h13] at h12
        nlinarith

      have h15 : x = 9 := by
        have h16 : x > 0 := hx1
        have h17 : x = Real.exp (log x) := by
          rw [Real.exp_log]
          all_goals linarith
        rw [h17, h14]
        have h18 : Real.exp (2 * log 3) = (Real.exp (log 3)) ^ 2 := by
          calc
            Real.exp (2 * log 3) = Real.exp (log 3 + log 3) := by ring_nf
            _ = Real.exp (log 3) * Real.exp (log 3) := by rw [Real.exp_add]
            _ = (Real.exp (log 3)) ^ 2 := by ring
        rw [h18]
        have h19 : Real.exp (log 3) = (3 : ℝ) := by
          rw [Real.exp_log]
          all_goals linarith
        rw [h19]
        all_goals norm_num

      right
      exact h15

  · -- Assume x = 1 / 27 ∨ x = 9, prove 2 * logb x 27 - 3 * logb 27 x = 1
    rintro (h_eq | h_eq)
    · -- Case 1: x = 1 / 27 
      rw [h_eq]
      have h1 : 2 * logb (1 / 27) 27 - 3 * logb 27 (1 / 27) = 2 * (log 27 / log (1 / 27)) - 3 * (log (1 / 27) / log 27) := by 
        have h2 : logb (1 / 27) 27 = log 27 / log (1 / 27) := by 
          field_simp [logb]
        have h3 : logb 27 (1 / 27) = log (1 / 27) / log 27 := by 
          field_simp [logb]
        rw [h2, h3]
      rw [h1]
      have h2 : log (27 : ℝ) > 0 := by 
        apply log_pos
        all_goals norm_num 
      have h3 : log (1 / 27 : ℝ) = - log (27 : ℝ) := by 
        simp [log_div, log_one]
      rw [h3]
      field_simp [h2]
      <;> ring_nf <;> field_simp [h2] 
    · -- Case 2: x = 9 
      rw [h_eq]
      have h1 : 2 * logb (9 : ℝ) 27 - 3 * logb 27 (9 : ℝ) = 2 * (log 27 / log (9 : ℝ)) - 3 * (log (9 : ℝ) / log 27) := by 
        have h2 : logb (9 : ℝ) 27 = log 27 / log (9 : ℝ) := by 
          field_simp [logb]
        have h3 : logb 27 (9 : ℝ) = log (9 : ℝ) / log 27 := by 
          field_simp [logb]
        rw [h2, h3]
      rw [h1]
      have h2 : log (27 : ℝ) > 0 := by 
        apply log_pos
        all_goals norm_num 
      have h3 : log (9 : ℝ) = 2 * log (3 : ℝ) := by 
        calc 
          log (9 : ℝ) = log (3 ^ 2) := by norm_num 
          _ = 2 * log (3 : ℝ) := by simp [log_pow]
      have h4 : log (27 : ℝ) = 3 * log (3 : ℝ) := by 
        calc 
          log (27 : ℝ) = log (3 ^ 3) := by norm_num 
          _ = 3 * log (3 : ℝ) := by simp [log_pow]
      rw [h3, h4]
      have h5 : log (3 : ℝ) > 0 := by 
        apply log_pos
        all_goals norm_num 
      field_simp [h5]
      <;> ring_nf <;> field_simp [h5]