import Mathlib

open BigOperators Real Set

theorem inequalities_270120 (a : ℝ) :
  (∀ x > 0, a - x - abs (log x) ≤ 0) ↔ a ≤ log (exp 1) - log (log (exp 1)) := by
  constructor
  · -- Assume ∀ x > 0, a - x - abs (log x) ≤ 0, prove a ≤ 1
    intro h
    have h1 := h 1 (by norm_num)
    have h2 : abs (log (1 : ℝ)) = 0 := by
      simp [log_one]
    rw [h2] at h1
    have h3 : a ≤ 1 := by nlinarith
    have h4 : log (exp 1) - log (log (exp 1)) = 1 := by
      have h5 : log (exp 1) = 1 := by
        rw [log_exp]
      have h6 : log (log (exp 1 : ℝ)) = 0 := by
        have h7 : log (exp 1 : ℝ) = 1 := by
          rw [log_exp]
        rw [h7]
        norm_num [log_one]
      linarith
    linarith
  · -- Assume a ≤ log (exp 1) - log (log (exp 1)), prove ∀ x > 0, a - x - abs (log x) ≤ 0
    intro ha x hx
    have h4 : log (exp 1) - log (log (exp 1)) = 1 := by
      have h5 : log (exp 1) = 1 := by
        rw [log_exp]
      have h6 : log (log (exp 1 : ℝ)) = 0 := by
        have h7 : log (exp 1 : ℝ) = 1 := by
          rw [log_exp]
        rw [h7]
        norm_num [log_one]
      linarith
    have h5 : a ≤ 1 := by
      linarith [ha, h4]
    have h10 : x + abs (log x) ≥ 1 := by
      by_cases h7 : log x ≥ 0
      · -- log x ≥ 0, so abs (log x) = log x
        rw [abs_of_nonneg h7]
        have h8 : x ≥ 1 := by
          by_contra h
          push_neg at h
          have h9 : log x < 0 := by
            have h11 : log x < log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h12 : log (1 : ℝ) = 0 := by
              simp [log_one]
            linarith
          linarith
        have h11 : x + log x ≥ (1 : ℝ) := by
          have h12 : log x ≥ (0 : ℝ) := by linarith
          have h13 : x ≥ (1 : ℝ) := by linarith
          have h14 : x + log x ≥ (1 : ℝ) := by
            have h15 : log x ≤ x - 1 := by
              linarith [Real.log_le_sub_one_of_pos hx]
            nlinarith
          linarith
        linarith
      · -- log x < 0, so abs (log x) = -log x
        rw [abs_of_neg (show log x < 0 by linarith)]
        have h77 : x < (1 : ℝ) := by
          by_contra h
          push_neg at h
          have h8 : log x ≥ (0 : ℝ) := by
            have h9 : log x ≥ (0 : ℝ) := by
              have h11 : log x ≥ log (1 : ℝ) := by
                apply Real.log_le_log
                all_goals linarith
              have h12 : log (1 : ℝ) = 0 := by
                simp [log_one]
              linarith
            linarith
          linarith
        have h11 : x - log x ≥ (1 : ℝ) := by
          have h12 : log x ≤ (0 : ℝ) := by linarith
          have h13 : x > 0 := by linarith
          have h14 : x - log x ≥ (1 : ℝ) := by
            have h15 : log x ≤ x - 1 := by
              linarith [Real.log_le_sub_one_of_pos hx]
            nlinarith
          linarith
        linarith
    linarith [abs_nonneg (log x)]