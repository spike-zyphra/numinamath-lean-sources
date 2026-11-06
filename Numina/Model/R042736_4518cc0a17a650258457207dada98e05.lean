import Mathlib

open Real

theorem inequalities_130342 :
    1 / logb 2 Real.pi + 1 / logb 5 Real.pi > 2 ∧
    1 / logb 2 Real.pi + 1 / logb Real.pi 2 > 2 := by
  constructor
  · 
    have h1 : 1 / logb 2 Real.pi + 1 / logb 5 Real.pi = (log 2 + log 5) / log Real.pi := by
      have h1 : 1 / logb 2 Real.pi = log 2 / log Real.pi := by
        field_simp [logb]
      have h2 : 1 / logb 5 Real.pi = log 5 / log Real.pi := by
        field_simp [logb]
      rw [h1, h2]
      ring
    rw [h1]
    have h2 : log 2 + log 5 = log (2 * 5) := by
      rw [log_mul (by norm_num) (by norm_num)]
    rw [h2]
    have h3 : log (2 * 5 : ℝ) = log 10 := by norm_num
    rw [h3]
    have h4 : Real.pi ^ 2 < 10 := by
      have h4 : Real.pi < 3.15 := Real.pi_lt_d2
      norm_num at h4
      nlinarith [h4, Real.pi_gt_three]
    have h5 : log Real.pi > 0 := by
      apply log_pos
      linarith [Real.pi_gt_three]
    have h6 : log (10 : ℝ) > 2 * log Real.pi := by
      have h7 : log (10 : ℝ) > log (Real.pi ^ 2) := by
        have h8 : log (Real.pi ^ 2) < log (10 : ℝ) := by
          apply Real.log_lt_log
          nlinarith [Real.pi_gt_three]
          all_goals linarith
        linarith
      have h8 : log (Real.pi ^ 2 : ℝ) = 2 * log Real.pi := by
        simp [log_pow]
      linarith [h7, h8]
    have h7 : (log (10 : ℝ) : ℝ) / log Real.pi > 2 := by
      have h5' : log Real.pi > 0 := h5
      apply (lt_div_iff' (by linarith)).mpr
      linarith [h6]
    linarith
  · 
    have h10 : 1 / logb 2 Real.pi = log 2 / log Real.pi := by
      field_simp [logb]
    have h11 : 1 / logb Real.pi 2 = log Real.pi / log 2 := by
      field_simp [logb]
    rw [h10, h11]
    have h12 : log 2 > 0 := by
      apply log_pos
      all_goals
        norm_num
    have h13 : log Real.pi > 0 := by
      apply log_pos
      linarith [Real.pi_gt_three]
    have h14 : log 2 / log Real.pi + log Real.pi / log 2 > 2 := by
      have h14 : log 2 / log Real.pi + log Real.pi / log 2 - 2 > 0 := by
        have h15 : log 2 / log Real.pi + log Real.pi / log 2 - 2 = (log 2 - log Real.pi) ^ 2 / (log 2 * log Real.pi) := by
          field_simp
          <;> ring
        rw [h15]
        have h16 : (log 2 - log Real.pi) ^ 2 > 0 := by
          have h17 : log 2 ≠ log Real.pi := by
            by_contra h
            have h18 : (2 : ℝ) = Real.pi := by
              have h19 : log 2 = log Real.pi := by
                linarith [h]
              have h20 : (2 : ℝ) > 0 := by norm_num
              have h21 : Real.pi > 0 := Real.pi_pos
              have h22 : (2 : ℝ) = Real.pi := by 
                exact log_injOn_pos (Set.mem_Ioi.mpr h20) (Set.mem_Ioi.mpr h21) h19
              assumption
            nlinarith [Real.pi_gt_three, show (2 : ℝ) < (3 : ℝ) by norm_num]
          have h18 : (log 2 - log Real.pi) ≠ 0 := by
            intro h
            apply h17
            linarith
          exact pow_two_pos_of_ne_zero h18
        have h17' : log 2 > 0 := h12
        have h17'' : log Real.pi > 0 := h13
        have h20 : log 2 * log Real.pi > 0 := mul_pos h17' h17''
        positivity
      linarith
    linarith