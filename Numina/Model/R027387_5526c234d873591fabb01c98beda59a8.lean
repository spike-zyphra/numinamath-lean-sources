import Mathlib

theorem algebra_167913 {x y : ℝ} (hx : x^2 - y^2 > 0) (hy : x + y > 0)
    (h : Real.logb 9 (x^3 + y^3) = Real.logb 3 (x^2 - y^2)) (h' : Real.logb 3 (x^2 - y^2) = Real.logb 3 (x + y)) :
    (x = 1 ∧ y = 0) ∨ (x = 2 ∧ y = 1) := by

  have eq1 : x^2 - y^2 = x + y := by
    have h1 : x^2 - y^2 > 0 := hx
    have h2 : x + y > 0 := hy
    have h3 : Real.logb 3 (x^2 - y^2) = Real.logb 3 (x + y) := h'
    have h4 : x^2 - y^2 = x + y := by
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) h3
    linarith [h4]

  have eq2 : x - y = 1 := by
    have h1 : x^2 - y^2 = x + y := eq1
    have h2 : x + y > 0 := hy
    have h3 : (x - y) * (x + y) = x + y := by
      nlinarith 
    have h4 : x + y > 0 := h2
    have h5 : x - y = 1 := by
      apply (mul_left_inj' (ne_of_gt h4)).mp
      linarith
    linarith

  have eq3 : x^3 + y^3 = (x + y)^2 := by
    have h1 : x^2 - y^2 > 0 := hx
    have h2 : x + y > 0 := hy
    have h3 : Real.logb 9 (x^3 + y^3) = Real.logb 3 (x^2 - y^2) := h

    have h4 : Real.logb 9 (x^3 + y^3) = (Real.logb 3 (x^3 + y^3)) / 2 := by 
      have h5 : Real.logb 9 (x^3 + y^3) = Real.logb 3 (x^3 + y^3) / Real.logb 3 (9:ℝ) := by 
        field_simp [Real.logb]
      have h6 : Real.logb 3 (9:ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h5, h6]

    rw [h4] at h3
    have h5 : Real.logb 3 (x^2 - y^2) = Real.logb 3 (x + y) := by linarith [h']
    have h6 : Real.logb 3 (x^3 + y^3) = 2 * Real.logb 3 (x + y) := by 
      linarith [h3, h5]

    have h7 : Real.logb 3 (x^3 + y^3) = Real.logb 3 ((x + y) ^ 2) := by 
      have h8 : Real.logb 3 ((x + y) ^ 2) = 2 * Real.logb 3 (x + y) := by 
        simp [Real.logb_pow]
      linarith [h6, h8]

    have h8 : x^3 + y^3 > 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y + 1), sq_nonneg (x + y - 1), sq_nonneg (x - 2), sq_nonneg (y - 1)]
    have h9 : (x + y) ^ 2 > 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y + 1), sq_nonneg (x + y - 1), sq_nonneg (x - 2), sq_nonneg (y - 1)]
    have h10 : x^3 + y^3 = (x + y) ^ 2 := by
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h8) (Set.mem_Ioi.mpr h9) h7
    linarith [h10]

  have h1 : x = y + 1 := by linarith [eq2]

  rw [h1] at eq3

  have eq4 : y * (2 * y^2 - y - 1) = 0 := by
    nlinarith

  have eq5 : y = 0 ∨ y = 1 := by
    have h1 : y * (2 * y^2 - y - 1) = 0 := eq4
    have h2 : 2 * y^2 - y - 1 = (2 * y + 1) * (y - 1) := by nlinarith 
    rw [h2] at h1
    cases (mul_eq_zero.1 h1) with
    | inl h3 => 
      left 
      linarith
    | inr h4 => 
      cases (mul_eq_zero.1 h4) with
      | inl h5 => 
        exfalso 
        nlinarith [sq_pos_of_pos hy]
      | inr h6 => 
        right 
        linarith

  cases eq5 with
  | inl hy0 => 
    have hx1 : x = 1 := by
      linarith [h1, hy0]
    left
    exact ⟨hx1, hy0⟩
  | inr hy1 => 
    have hx2 : x = 2 := by
      linarith [h1, hy1]
    right
    exact ⟨hx2, hy1⟩