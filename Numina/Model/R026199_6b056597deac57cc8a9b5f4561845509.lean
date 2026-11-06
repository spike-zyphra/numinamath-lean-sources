import Mathlib

open Real Set

theorem algebra_93837 {x : ℝ} (hx : 0 < x) (h : logb 10 x < 0) : x ∈ Ioo 0 1 := by
  have h1 : x < 1 := by
    by_contra h2
    push_neg at h2
    have h2' : logb 10 x ≥ 0 := by
      have h4 : x ≥ 1 := by linarith
      have h5 : logb 10 x ≥ 0 := by
        have h6 : logb 10 x = (log x) / (log (10 : ℝ)) := by
          field_simp [logb]
        have h7 : log (10 : ℝ) > 0 := by
          apply log_pos
          norm_num
        have h8 : log x ≥ 0 := by
          have h9 : x ≥ 1 := by linarith
          have h10 : log x ≥ log (1 : ℝ) := by
            apply Real.log_le_log
            linarith
            linarith
          have h11 : log (1 : ℝ) = 0 := by
            simp [log_one]
          linarith
        have h12 : (log x) / (log (10 : ℝ)) ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        linarith [h6, h12]
      linarith
    linarith
  constructor
  · exact hx
  · exact h1