import Mathlib

theorem algebra_307174 (x : ℝ) (hx : x > 0) (h : Real.logb x 10 = Real.logb 4 100) :
    x = 2 := by
  have h1 : Real.logb 4 100 = Real.logb 2 10 := by
    have h2 : Real.logb 4 100 = Real.log 100 / Real.log 4 := by
      field_simp [Real.logb]
    have h3 : Real.logb 2 10 = Real.log 10 / Real.log 2 := by
      field_simp [Real.logb]
    have h4 : Real.log 100 = 2 * Real.log 10 := by
      calc
        Real.log 100 = Real.log (10 ^ 2) := by norm_num
        _ = 2 * Real.log 10 := by simp [Real.log_pow]
    have h5 : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log (2  ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]
    rw [h2, h3]
    rw [h4, h5]
    <;> ring_nf <;> field_simp
  rw [h1] at h
  by_cases h4 : x = 1
  · -- Assume x = 1.
    rw [h4] at h
    -- Show contradiction: $\logb 1 10 = 0$ and $\logb 4 100 > 0$
    have h4 : Real.logb (1 : ℝ) 10 = 0 := by
      simp [Real.logb]
      <;> linarith
    have h5 : Real.logb (4 : ℝ) 100 > 0 := by
      have h11 : Real.logb (4 : ℝ) 100 = Real.log 100 / Real.log 4 := by
        field_simp [Real.logb]
      rw [h11]
      have h6 : Real.log (100 : ℝ) > 0 := by
        apply Real.log_pos
        all_goals norm_num
      have h7 : Real.log (4 : ℝ) > 0 := by
        apply Real.log_pos
        all_goals norm_num
      have h8 : Real.log (100 : ℝ) / Real.log (4 : ℝ) > 0 := by
        apply div_pos
        all_goals linarith
      linarith
    linarith [h4, h5]
  · -- Now x ≠ 1.
    have h6 : Real.log x ≠ 0 := by
      by_contra h
      have : x = 1 := by
        have h8 : Real.log x = 0 := by linarith [h]
        rw [Real.log_eq_zero] at h8
        rcases h8 with (r | r | r)
        · linarith
        · linarith
        · linarith
      contradiction
    have h7 : Real.log 2 = Real.log x := by
      have h2 : Real.logb x 10 = Real.log 10 / Real.log x := by
        field_simp [Real.logb]
      have h3 : Real.logb 2 10 = Real.log 10 / Real.log 2 := by
        field_simp [Real.logb]
      rw [h2, h3] at h
      field_simp [show Real.log 10 ≠ 0 by apply ne_of_gt; apply Real.log_pos; all_goals norm_num, h6] at h
      all_goals nlinarith
    have h8 : x = (2 : ℝ) := by
      have h9 : Real.log (x : ℝ) = Real.log (2 : ℝ) := by
        linarith [h7]
      have h10 : x > 0 := hx
      have h11 : (2 : ℝ) > 0 := by norm_num
      have h12 : x = (2 : ℝ) := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (by norm_num)) h9
      exact h12
    exact h8