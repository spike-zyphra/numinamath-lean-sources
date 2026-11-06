import Mathlib

open Real

theorem algebra_136936 (a : ℝ) (ha : 0 < a ∧ a ≠ 1) :
    logb a (sqrt 2) < 1 ↔ 0 < a ∧ a < 1 ∨ sqrt 2 < a := by
  have h1 : logb a (sqrt 2) = (log (sqrt 2) ) / (log a) := by
    field_simp [logb]
  have h2 : log (sqrt 2) = (1 / 2) * log 2 := by
    calc
      log (sqrt 2) = log ((2 : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
      _ = (1 / 2 : ℝ) * log (2 : ℝ) := by
        rw [log_rpow]
        all_goals norm_num
  rw [h1, h2]
  constructor
  · -- Assume the inequality holds, prove 0 < a ∧ a < 1 ∨ sqrt 2 < a
    intro h
    have h3 : 0 < a := ha.1
    have h4 : a ≠ 1 := ha.2
    by_cases h5 : a < 1
    · -- Case 0 < a < 1
      have h6 : log a < 0 := by
        have h7 : log a < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals linarith
        have h8 : log (1 : ℝ) = 0 := Real.log_one
        linarith
      left
      constructor
      · linarith
      · linarith
    · -- Case a ≥ 1
      have h5' : a ≥ 1 := by
        by_contra h8
        push_neg at h8
        have h6 : a < 1 := by linarith
        linarith [h5, h6]
      have h8 : a > 1 := by
        by_contra h4
        push_neg at h4
        have h9 : a = 1 := by
          linarith
        tauto
      have h11 : log a > 0 := by
        have h12 : log a > log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals linarith
        have h13 : log (1 : ℝ) = 0 := Real.log_one
        linarith
      have h10 : (1 / 2) * log 2 < log a := by
        have h4' : ( (1 / 2) * log 2 ) / (log a) < 1 := by
          simpa using h
        have h14 : ( (1 / 2) * log 2 ) < log a := by
          have h15 : log a > 0 := h11
          apply (div_lt_iff₀ h15).mp at h4'
          linarith
        linarith
      have h13 : sqrt 2 < a := by
        have h4'' : log a > log (sqrt 2 : ℝ) := by
          linarith [h10, h2]
        have h5'' : a > (sqrt 2 : ℝ) := by
          by_contra h6
          push_neg at h6
          have h7 : log a ≤ log (sqrt 2 : ℝ) := by
            apply Real.log_le_log
            all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), h6]
          linarith [h4'', h7]
        linarith
      right
      linarith
  · -- Assume 0 < a ∧ a < 1 ∨ sqrt 2 < a, prove the inequality
    rintro (h | h)
    · -- Assume 0 < a ∧ a < 1
      have h3 : a < 1 := h.2
      have h4 : 0 < a := h.1
      have h6 : log a < 0 := by
        have h7 : log a < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals linarith
        have h8 : log (1 : ℝ) = 0 := Real.log_one
        linarith
      have h7 : ( (1 / 2) * log 2 ) / (log a) < 1 := by
        apply (div_lt_iff_of_neg' (by linarith)).mpr
        nlinarith [show log (2 : ℝ) > 0 by apply log_pos; all_goals norm_num]
      linarith
    · -- Assume sqrt 2 < a
      have h3 : a > (sqrt 2 : ℝ) := by linarith [h]
      have h4 : 0 < a := ha.1
      have h6 : log a > 0 := by
        have h8 : (sqrt 2 : ℝ) > 1 := by
          nlinarith [show (2 : ℝ) < (4 : ℝ) by norm_num, Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h9 : a > 1 := by
          nlinarith [h3, h8]
        have h10 : log a > log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals linarith
        have h11 : log (1 : ℝ) = 0 := Real.log_one
        linarith
      have h10 : (1 / 2) * log 2 < log a := by
        have h4'' : log a > log (sqrt 2 : ℝ) := by
          have h7 : a > (sqrt 2 : ℝ) := h3
          apply Real.log_lt_log
          all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
        linarith [h4'', h2]
      have h7 : ( (1 / 2) * log 2 ) / (log a) < 1 := by
        apply (div_lt_iff₀ h6).mpr
        nlinarith
      linarith