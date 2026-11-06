import Mathlib

theorem algebra_311669 {x : ℝ} (hx : x > 0) (h : Real.sqrt x - 1 / Real.sqrt x = -Real.sqrt 2) :
    x^2 - 1 / x^2 = -8 * Real.sqrt 3 := by

  have h1 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.mpr
    exact hx

  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  
  have h3 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = x + 1 / x - 2 := by
    field_simp [h1]
    <;> nlinarith [Real.sqrt_nonneg x, h2]

  have h4 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = 2 := by 
    rw [h]
    have h5 : (-Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    linarith [h5]

  have h5 : x + 1 / x = 4 := by
    linarith [h3, h4]

  have h6 : Real.sqrt x + 1 / Real.sqrt x = Real.sqrt 6 := by
    have h7 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = 6 := by
      have h8 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = x + 1 / x + 2 := by
        field_simp [h1]
        <;> nlinarith [Real.sqrt_nonneg x, h2]
      rw [h8, h5]
      all_goals norm_num
    have h8 : Real.sqrt 6 ≥ 0 := by
      apply Real.sqrt_nonneg
    have h11 : (Real.sqrt x + 1 / Real.sqrt x) ≥ 0 := by
      have h9 : Real.sqrt x > 0 := h1
      have h10 : 1 / Real.sqrt x > 0 := by
        positivity
      linarith [h9, h10]
    have h12 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
    have h13 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = (Real.sqrt 6) ^ 2 := by
      rw [h7, h12]
    nlinarith [h11, Real.sqrt_nonneg 6]

  have h7 : x - 1 / x = -2 * Real.sqrt 3 := by
    calc
      x - 1 / x = (Real.sqrt x - 1 / Real.sqrt x) * (Real.sqrt x + 1 / Real.sqrt x) := by
        field_simp [h1]
        <;> nlinarith [Real.sqrt_nonneg x, h2]
      _ = (-Real.sqrt 2) * (Real.sqrt 6) := by 
        rw [h, h6]
      _ = -2 * Real.sqrt 3 := by
        have h8 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h8]
        nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]

  have h8 : x^2 - 1 / x^2 = (x - 1 / x) * (x + 1 / x) := by
    field_simp
    <;> ring
  
  rw [h8, h7, h5]
  all_goals ring