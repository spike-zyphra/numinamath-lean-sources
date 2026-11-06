import Mathlib

theorem algebra_134451 (x : ℝ) (hx : 0 < x) :
    6 ^ Real.logb 10 x + x ^ Real.logb 10 6 = 72 ↔ x = 100 := by
  constructor
  · -- Assume 6 ^ Real.logb 10 x + x ^ Real.logb 10 6 = 72. Prove x = 100
    intro h
    have h1 : 6 ^ Real.logb 10 x + x ^ Real.logb 10 6 = 72 := h
    have h2 : (x : ℝ) ^ Real.logb 10 6 = (6 : ℝ) ^ Real.logb 10 x := by
      have h_eq1 : Real.logb 10 (x ^ Real.logb 10 6) = Real.logb 10 (6 ^ Real.logb 10 x) := by
        have h4 : Real.logb 10 (x ^ Real.logb 10 6) = Real.logb 10 6 * Real.logb 10 x := by
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals linarith
        have h5 : Real.logb 10 (6 ^ Real.logb 10 x) = Real.logb 10 x * Real.logb 10 6 := by
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals linarith
        rw [h4, h5]
        all_goals nlinarith
      have h3 : x ^ Real.logb 10 6 > 0 := by positivity
      have h4 : (6 : ℝ) ^ Real.logb 10 x > 0 := by positivity
      have h7 : Real.logb 10 (x ^ Real.logb 10 6) = Real.logb 10 (6 ^ Real.logb 10 x) := h_eq1
      have h8 : x ^ Real.logb 10 6 = (6 : ℝ) ^ Real.logb 10 x := by
        apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h3) (Set.mem_Ioi.mpr h4) h7
      exact_mod_cast h8
    rw [h2] at h1
    have h_eq3 : (6 : ℝ) ^ Real.logb 10 x = 36 := by
      nlinarith
    have h_eq4 : Real.logb 10 (6 ^ Real.logb 10 x) = Real.logb 10 (36 : ℝ) := by
      rw [h_eq3]
    have h_eq7 : Real.logb 10 (6 ^ Real.logb 10 x) = Real.logb 10 x * Real.logb 10 6 := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
      all_goals linarith
    have h_eq8 : Real.logb 10 (36 : ℝ) = 2 * Real.logb 10 6 := by
      calc
        Real.logb 10 (36 : ℝ) = Real.logb 10 (6 ^ 2) := by norm_num
        _ = 2 * Real.logb 10 6 := by
          simp [Real.logb_pow]
          <;> nlinarith
    rw [h_eq7] at h_eq4
    have h_eq9 : Real.logb 10 6 > (0 : ℝ) := by
      have h10 : Real.logb 10 6 > (0 : ℝ) := by
        apply Real.logb_pos
        all_goals norm_num
      linarith
    have h_eq10 : Real.logb 10 x = (2 : ℝ) := by
      have h_eq11 : Real.logb 10 x * Real.logb 10 6 = 2 * Real.logb 10 6 := by
        nlinarith [h_eq4, h_eq8]
      have h_eq12 : Real.logb 10 6 ≠ 0 := by
        nlinarith [h_eq9]
      have h_eq13 : Real.logb 10 x = 2 := by
        apply (mul_left_inj' h_eq12).mp
        linarith
      exact_mod_cast h_eq13
    have h_eq11 : x = (10 : ℝ) ^ (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h_eq10
      all_goals
        try norm_num at h_eq10 ⊢
        all_goals
          try nlinarith
          all_goals
            norm_num at h_eq10 ⊢
    have h_eq12 : x = 100 := by
      have h_eq13 : x = (10 : ℝ) ^ (2 : ℝ) := h_eq11
      rw [h_eq13]
      norm_num
    linarith
  · -- Assume x = 100, prove the equation
    intro h
    rw [h]
    have h1 : Real.logb 10 (100 : ℝ) = (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h2 : (6 : ℝ) ^ Real.logb 10 (100 : ℝ) = 36 := by
      rw [h1]
      have h3 : (6 : ℝ) ^ (2 : ℝ) = (36 : ℝ) := by
        norm_num
      linarith
    have h3 : (100 : ℝ) ^ Real.logb 10 (6 : ℝ) = (6 : ℝ) ^ (2 : ℝ) := by
      have h4 : (100 : ℝ) ^ Real.logb 10 (6 : ℝ) = (6 : ℝ) ^ Real.logb 10 (100 : ℝ) := by
        have h5 : Real.logb 10 ((100 : ℝ) ^ Real.logb 10 (6 : ℝ)) = Real.logb 10 ((6 : ℝ) ^ Real.logb 10 (100 : ℝ)) := by
          have h6 : Real.logb 10 ((100 : ℝ) ^ Real.logb 10 (6 : ℝ)) = Real.logb 10 (6 : ℝ) * Real.logb 10 (100 : ℝ) := by
            rw [Real.logb_rpow_eq_mul_logb_of_pos]
            all_goals norm_num
          have h7 : Real.logb 10 ((6 : ℝ) ^ Real.logb 10 (100 : ℝ)) = Real.logb 10 (100 : ℝ) * Real.logb 10 (6 : ℝ) := by
            rw [Real.logb_rpow_eq_mul_logb_of_pos]
            all_goals norm_num
          rw [h6, h7]
          <;> try nlinarith
          all_goals
            linarith
        have h3 : (100 : ℝ) ^ Real.logb 10 (6 : ℝ) > 0 := by positivity
        have h4 : (6 : ℝ) ^ Real.logb 10 (100 : ℝ) > 0 := by positivity
        have h5' : Real.logb 10 ((100 : ℝ) ^ Real.logb 10 (6 : ℝ)) = Real.logb 10 ((6 : ℝ) ^ Real.logb 10 (100 : ℝ)) := h5
        have h6 : (100 : ℝ) ^ Real.logb 10 (6 : ℝ) = (6 : ℝ) ^ Real.logb 10 (100 : ℝ) := by
          apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h3) (Set.mem_Ioi.mpr h4) h5'
        exact_mod_cast h6
      rw [h4, h1]
      <;> norm_num
      <;> nlinarith
    have h4 : (6 : ℝ) ^ Real.logb 10 (100 : ℝ) = 36 := h2
    have h5 : (100 : ℝ) ^ Real.logb 10 (6 : ℝ) = 36 := by
      rw [h3]
      all_goals norm_num
      <;> norm_num
      <;> nlinarith
    linarith