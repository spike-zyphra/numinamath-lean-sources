import Mathlib

open Real

theorem algebra_184686 {x : ℝ} (hx : x > 0) (a : ℝ) (ha : a > 0 ∧ a ≠ 1)
    (h : logb a x = x) (h' : a = x ^ logb 4 x) :
    x = 2 := by
  have h1 : logb a x = x := h
  rw [h'] at h1
  have h2 : logb (x ^ logb 4 x) x = x := h1
  have h3 : logb (x ^ logb 4 x) x = 1 / logb 4 x := by
    have h4 : logb (x ^ logb 4 x) x = (log x) / (log (x ^ logb 4 x)) := by 
      field_simp [logb]
    have h5 : log (x ^ logb 4 x) = log x * logb 4 x := by 
      rw [log_rpow]
      all_goals linarith 
    have h6 : log x ≠ 0 := by
      by_contra h7 
      have : x = 1 := by
        have h8 : log x = 0 := by linarith 
        rw [Real.log_eq_zero] at h8
        rcases h8 with (r | r | r)
        · linarith
        · linarith
        · linarith 
      rw [this] at h'
      have ha1 : a = 1 := by
        norm_num [this, Real.logb_one] at h'
        all_goals linarith 
      have ha1' : a ≠ 1 := ha.2 
      contradiction 
    have h7 : logb 4 x ≠ 0 := by
      by_contra h9 
      have h8 : logb 4 x = 0 := by linarith 
      have h : a = 1 := by
        rw [h'] 
        rw [h8] 
        norm_num 
      have ha1 : a ≠ 1 := ha.2 
      contradiction 
    rw [h4, h5] 
    field_simp [h6, h7] 
    <;> nlinarith 
  have h4' : (1 / logb 4 x : ℝ) = x := by
    linarith [h2, h3]
  have h5' : logb 4 x = 1 / x := by
    have h7 : (1 / logb 4 x : ℝ) = x := h4'
    have h8 : logb 4 x ≠ 0 := by 
      by_contra h9
      have h : a = 1 := by
        rw [h'] 
        rw [h9] 
        norm_num 
      have ha1 : a ≠ 1 := ha.2 
      contradiction 
    field_simp at h7 ⊢ 
    <;> nlinarith 
  have h8 : logb 4 x = (log x) / (log (4 : ℝ)) := by 
    field_simp [logb]
  have h9 : (log x) / (log (4 : ℝ)) = 1 / x := by
    linarith [h5', h8]
  have h10 : x * log x = log (4 : ℝ) := by 
    field_simp [(show log (4 : ℝ) ≠ 0 by
      have h7' : (4 : ℝ) > 1 := by norm_num 
      have h8' : log (4 : ℝ) > 0 := by 
        apply Real.log_pos 
        all_goals linarith 
      linarith 
    )] at h9 ⊢ 
    nlinarith 
  have h11 : x * log x = 2 * log (2 : ℝ) := by 
    rw [show log (4 : ℝ) = 2 * log (2 : ℝ) by 
      calc 
        log (4 : ℝ) = log ((2 : ℝ) ^ 2) := by norm_num 
        _ = 2 * log (2 : ℝ) := by simp [log_pow]
    ] at h10 
    linarith 
  by_cases h2' : x < (2 : ℝ)
  · -- Assume x < 2 
    have h4' : x * log x < (2 * log (2 : ℝ)) := by
      have h5' : log x < log (2 : ℝ) := by 
        apply Real.log_lt_log 
        all_goals linarith 
      nlinarith [h5', sq_nonneg (x - 1), sq_nonneg (log x - log (2 : ℝ)), 
        h5', Real.log_pos (show (2 : ℝ) > 1 by norm_num), 
        mul_pos hx (show 0 < log (2 : ℝ) by apply log_pos; all_goals norm_num)
      ]
    linarith [h11, h4']
  · -- Assume x ≥ 2 
    by_cases h3' : x > (2 : ℝ)
    · -- Assume x > 2 
      have h4' : x * log x > (2 * log (2 : ℝ)) := by 
        have h5' : log x > log (2 : ℝ) := by 
          apply Real.log_lt_log 
          all_goals linarith 
        nlinarith [h5', sq_nonneg (x - 2), sq_nonneg (log x - log (2 : ℝ)), 
          h5', Real.log_pos (show (2 : ℝ) > 1 by norm_num), 
          mul_pos hx (show 0 < log (2 : ℝ) by apply log_pos; all_goals norm_num)
        ]
      linarith [h11, h4']
    · -- Assume x = 2 
      linarith