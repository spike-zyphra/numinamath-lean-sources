import Mathlib

open BigOperators Real Set

theorem inequalities_325717 (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
  (h : ∀ x > 0, a^x ≥ x ∧ x ≥ logb a x) :
  a ≥ exp (1 / exp 1) := by
  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  by_cases ha3 : a > 1
  · -- a > 1, so log a > 0
    have h1 := (h (Real.exp 1) (by positivity)).2
    have h2 : Real.exp 1 ≥ logb a (Real.exp 1) := by linarith [h1]
    have h3 : logb a (Real.exp 1) = (log (Real.exp 1) ) / (log a) := by
      field_simp [logb]
    have h4 : log (Real.exp 1) = 1 := by
      rw [log_exp]
    rw [h3, h4] at h2
    have h5 : log a > 0 := by
      apply log_pos
      linarith
    have h6 : log a ≥ 1 / exp 1 := by
      have h7 : (Real.exp 1) * (log a) ≥ 1 := by
        have h8 : 0 < log a := h5
        have h9 : Real.exp 1 ≥ (1 / (log a) : ℝ) := by
          linarith [h2]
        have h10 : (Real.exp 1) * (log a) ≥ 1 := by
          have h11 : 0 < log a := h5
          have h12 : (1 / (log a) : ℝ) ≤ Real.exp 1 := by linarith [h9]
          have h13 : (1 / (log a)) * (log a) ≤ (Real.exp 1) * (log a) := by
            have h14 : 0 < log a := h5
            apply mul_le_mul_of_nonneg_right
            linarith [h12]
            all_goals
              linarith
          have h14 : (1 / (log a)) * (log a) = 1 := by
            field_simp [show log a ≠ 0 by linarith]
          nlinarith
        linarith
      have h71 : log a ≥ 1 / exp 1 := by
        by_contra h
        push_neg at h
        have h72 : (Real.exp 1) * (log a) < 1 := by
          have h73 : log a < 1 / exp 1 := by linarith
          have h74 : (Real.exp 1) * (log a) < (Real.exp 1) * (1 / exp 1) := by
            apply mul_lt_mul_of_pos_left
            linarith
            positivity
          have h75 : (Real.exp 1) * (1 / exp 1) = 1 := by
            field_simp
          nlinarith
        nlinarith
      linarith
    have h11 : a ≥ exp (1 / exp 1) := by
      have h12 : log a ≥ 1 / exp 1 := h6
      have h13 : a = Real.exp (log a) := by
        rw [Real.exp_log]
        all_goals
          linarith
      have h14 : Real.exp (log a) ≥ Real.exp (1 / exp 1) := by
        apply Real.exp_le_exp_of_le
        linarith [h12]
      have h15 : Real.exp (1 / exp 1) = exp (1 / exp 1) := by
        rfl
      linarith [h13, h14, h15]
    linarith
  · -- a ≤ 1
    have ha4 : a ≤ 1 := by linarith
    have ha5 : a < 1 := by
      by_contra h8
      push_neg at h8
      have h9 : a ≥ 1 := by linarith
      have h10 : a = 1 := by
        linarith
      tauto
    -- Now $0 < a < 1$.
    -- In this case, $\log a < 0$.
    have h18 := (h (Real.exp 1) (by positivity)).1
    have h9 : a ^ (Real.exp 1) ≥ Real.exp 1 := by linarith [h18]
    have h10 : a ^ (Real.exp 1) < Real.exp 1 := by
      have h11 : a ^ (Real.exp 1) < (1 : ℝ) := by
        have h12 : a < (1 : ℝ) := by linarith
        have h17 : a ^ (Real.exp 1) < (1 : ℝ) := by
          apply Real.rpow_lt_one
          all_goals
            try linarith
            try positivity
        linarith
      have h100 : (1 : ℝ) < Real.exp 1 := by
        have h101 : Real.exp 1 > (1 : ℝ) := by
          have h102 : Real.exp (1 : ℝ) > 1 := by
            have h103 : Real.exp (0 : ℝ) = 1 := Real.exp_zero
            have h104 : Real.exp (1 : ℝ) > Real.exp (0 : ℝ) := by
              apply Real.exp_strictMono
              all_goals
                linarith
            have h105 : Real.exp (0 : ℝ) = 1 := Real.exp_zero
            linarith
          linarith
        linarith
      linarith
    linarith