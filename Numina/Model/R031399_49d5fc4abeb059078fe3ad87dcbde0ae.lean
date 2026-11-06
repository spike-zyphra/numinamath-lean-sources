import Mathlib

theorem algebra_167062 (x : ℝ) (hx : x > 0) (h : Real.logb x 3 + Real.logb 3 x = Real.logb (Real.sqrt x) 3 + Real.logb 3 (Real.sqrt x) + 0.5) :
    x = 1 / 3 ∨ x = 9 := by

  have h1 : x ≠ 1 := by
    by_contra h1
    rw [h1] at h
    have h2 : Real.logb (1 : ℝ) 3 = 0 := by
      simp [Real.logb_one]
    have h3 : Real.logb (Real.sqrt (1 : ℝ)) 3 = 0 := by
      have h4 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      rw [h4]
      simp [Real.logb_one]
    have h5 : Real.logb (3 : ℝ) (Real.sqrt (1 : ℝ)) = 0 := by
      have h4 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      rw [h4]
      simp [Real.logb_one]
    simp [h2, h3, h5] at h
    all_goals linarith

  have h2 : Real.logb x 3 = 1 / Real.logb 3 x := by
    field_simp [Real.logb]

  have h3 : Real.logb (Real.sqrt x) 3 = 2 / Real.logb 3 x := by
    have h4 : Real.logb (Real.sqrt x) 3 = Real.logb 3 3 / Real.logb 3 (Real.sqrt x) := by
      field_simp [Real.logb]
    have h5 : Real.logb 3 (Real.sqrt x) = (1 / 2) * Real.logb 3 x := by
      rw [show Real.sqrt x = x ^ (1 / 2 : ℝ) by rw [Real.sqrt_eq_rpow]]
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try norm_num
        try linarith
    rw [h4, h5]
    have h10 : Real.logb 3 3 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [h10]
    <;> ring_nf

  have h6 : Real.logb 3 (Real.sqrt x) = (1 / 2) * Real.logb 3 x := by
    rw [show Real.sqrt x = x ^ (1 / 2 : ℝ) by rw [Real.sqrt_eq_rpow]]
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals
      try norm_num
      try linarith

  rw [h2, h3, h6] at h

  have h7 : Real.logb 3 x ≠ 0 := by
    by_contra h7
    have h8 : Real.logb 3 x = 0 := by linarith
    have h9 : x = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] at h8
      · linarith
      all_goals
        try norm_num
        try linarith
    tauto

  have eq1 : (Real.logb 3 x) ^ 2 - (Real.logb 3 x) - 2 = 0 := by
    have eq9 : (Real.logb 3 x) * (1 / Real.logb 3 x + Real.logb 3 x) = (Real.logb 3 x) * (2 / Real.logb 3 x + (1 / 2) * Real.logb 3 x + 0.5) := by
      have eq10 : 1 / Real.logb 3 x + Real.logb 3 x = 2 / Real.logb 3 x + (1 / 2) * Real.logb 3 x + 0.5 := by
        linarith [h]
      rw [eq10]
    have eq14 : (Real.logb 3 x) * (1 / Real.logb 3 x + Real.logb 3 x) = 1 + (Real.logb 3 x) ^ 2 := by
      have eq14 : (Real.logb 3 x) * (1 / Real.logb 3 x + Real.logb 3 x) = (Real.logb 3 x) * (1 / Real.logb 3 x) + (Real.logb 3 x) ^ 2 := by ring
      have eq15 : (Real.logb 3 x) * (1 / Real.logb 3 x) = 1 := by
        field_simp [h7]
      rw [eq14, eq15]
    have eq16 : (Real.logb 3 x) * (2 / Real.logb 3 x + (1 / 2) * Real.logb 3 x + 0.5) = 2 + (1 / 2) * (Real.logb 3 x) ^ 2 + 0.5 * (Real.logb 3 x) := by
      have eq17 : (Real.logb 3 x) * (2 / Real.logb 3 x + (1 / 2) * Real.logb 3 x + 0.5) =
          (Real.logb 3 x) * (2 / Real.logb 3 x) + (Real.logb 3 x) * ((1 / 2) * Real.logb 3 x) + (Real.logb 3 x) * (0.5 : ℝ) := by ring
      have eq18 : (Real.logb 3 x) * (2 / Real.logb 3 x) = 2 := by
        field_simp [h7]
      rw [eq17, eq18]
      all_goals
        ring_nf
    rw [eq14, eq16] at eq9
    ring_nf at eq9 ⊢
    nlinarith

  have eq20 : (Real.logb 3 x - 2) * (Real.logb 3 x + 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 eq20) with h8 h9
  · -- When Real.logb 3 x - 2 = 0
    have h10 : Real.logb 3 x = 2 := by linarith
    have h11 : x = 9 := by
      have h12 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
        field_simp
      rw [h12, h10]
      norm_num
    right
    linarith
  · -- When Real.logb 3 x + 1 = 0
    have h10 : Real.logb 3 x = -1 := by linarith
    have h11 : x = (1 / 3 : ℝ) := by
      have h12 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
        field_simp
      rw [h12, h10]
      norm_num
    left
    linarith