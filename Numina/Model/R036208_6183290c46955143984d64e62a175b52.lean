import Mathlib

theorem algebra_10335 {x : ℝ} (hx : 0 < x ∧ x ≠ 1) :
    Real.logb x 81 = Real.logb 2 16 ↔ x = 3 := by
  have h1 : Real.logb 2 16 = 4 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  rw [h1]
  constructor
  · -- First direction: if $\log_x 81 = 4$, then $x = 3$.
    intro h
    have h2 : Real.logb x 81 = 4 := h
    have h3 : Real.logb x 81 = Real.log 81 / Real.log x := by
      field_simp [Real.logb]
    rw [h3] at h2 
    have h4 : Real.log 81 = 4 * (Real.log 3) := by
      calc
        Real.log 81 = Real.log ((3: ℝ) ^ 4) := by norm_num
        _ = 4 * Real.log 3 := by simp [Real.log_pow]
    have h6 : Real.log 81 = 4 * Real.log x := by
      have h7 : Real.log x ≠ 0 := by
        have hx' : x > 0 := hx.1
        have hx'' : x ≠ 1 := hx.2
        have h8 : Real.log x ≠ 0 := by
          by_contra h
          have : x = 1 := by
            rw [Real.log_eq_zero] at h
            rcases h with (r | r | r)
            · linarith
            · linarith
            · linarith
          tauto
        assumption
      have h11 : Real.log 81 / Real.log x = 4 := by
        linarith
      have h10 : Real.log x ≠ 0 := h7
      have h9 : Real.log 81 = 4 * Real.log x := by
        field_simp [h10] at h11 ⊢
        nlinarith
      assumption
    -- From $h4$ and $h6$, we have $4 * \log 3 = 4 * \log x$, so $\log 3 = \log x$.
    have h10 : Real.log 3 = Real.log x := by
      nlinarith [h4, h6]
    -- From $\log 3 = \log x$, we have $3 = x$.
    have h3_pos : (0 : ℝ) < 3 := by linarith
    have hx_pos : x > 0 := hx.1
    have h3_eq_x : (3 : ℝ) = x := by
      have h13 : Real.log 3 = Real.log x := h10
      have h14 : (0 : ℝ) < 3 := by linarith
      have h15 : x > 0 := hx.1
      have hx_mem : x ∈ Set.Ioi (0 : ℝ) := by
        exact Set.mem_Ioi.mpr h15
      have h3_mem : (3 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
        exact Set.mem_Ioi.mpr h14
      have log_eq : Real.log 3 = Real.log x := h10
      have h_eq1 : (3 : ℝ) = x := by
        have h3_eq5 : x = (3 : ℝ) := by
          apply Real.log_injOn_pos hx_mem h3_mem
          all_goals 
          try { nlinarith [log_eq] }
          all_goals linarith
          all_goals nlinarith
        -- Now we need to show 3 = x from x = 3
        nlinarith [h3_eq5]
      assumption
    -- From $3 = x$, we get $x = 3$.
    linarith
  · -- Second direction: if $x = 3$, then $\log_x 81 = 4$.
    intro h
    rw [h]
    have h12 : Real.logb (3 : ℝ) 81 = 4 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      all_goals norm_num
    assumption
  all_goals try linarith
  all_goals try tauto