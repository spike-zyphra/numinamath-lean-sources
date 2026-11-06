import Mathlib

theorem algebra_326798 {x : ℝ} (hx : x > 0) (h : Real.sqrt x - 1 / Real.sqrt x = -2) :
    x^2 - 1 / x^2 = -24 * Real.sqrt 2 := by
  have h1 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.2
    exact hx
  have eq1 : x - 1 = -2 * Real.sqrt x := by
    have h2 : Real.sqrt x ≠ 0 := by
      linarith
    have eq2 : (Real.sqrt x - 1 / Real.sqrt x) * Real.sqrt x = -2 * Real.sqrt x := by
      rw [h]
      all_goals nlinarith
    have eq3 : (Real.sqrt x - 1 / Real.sqrt x) * Real.sqrt x = x - 1 := by
      field_simp [h1]
      <;> nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
    linarith [eq2, eq3]
  have h5 : x + 1 / x = 6 := by
    have h6 : Real.sqrt x - 1 / Real.sqrt x = -2 := h
    have h7 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = 4 := by
      rw [h6]
      all_goals norm_num
    have h8 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = x + 1 / x - 2 := by
      field_simp [h1]
      <;> nlinarith [h1, Real.sq_sqrt (show 0 ≤ x by linarith)]
    linarith [h7, h8]
  have h10 : Real.sqrt x + 1 / Real.sqrt x = 2 * Real.sqrt 2 := by
    have h11 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = 8 := by
      have h12 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = x + 1 / x + 2 := by
        field_simp [h1]
        <;> nlinarith [h1, Real.sq_sqrt (show 0 ≤ x by linarith)]
      nlinarith [h5, h12]
    have h13 : Real.sqrt x + 1 / Real.sqrt x ≥ 0 := by
      have h100 : Real.sqrt x > 0 := h1
      positivity
    have h14 : (Real.sqrt x + 1 / Real.sqrt x) = Real.sqrt (8 : ℝ) := by
      have h15 : ((Real.sqrt x + 1 / Real.sqrt x) ^ 2) = (8 : ℝ) := h11
      have h16 : Real.sqrt x + 1 / Real.sqrt x ≥ 0 := h13
      have h17 : Real.sqrt (8 : ℝ) ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show 0 ≤ (8 : ℝ) by norm_num), h15, Real.sqrt_nonneg (8 : ℝ)]
    have h18 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num [mul_add, pow_two]
    rw [h18] at h14
    linarith
  have h11 : x - 1 / x = -4 * Real.sqrt 2 := by
    have h12 : (x - 1 / x) = (Real.sqrt x - 1 / Real.sqrt x) * (Real.sqrt x + 1 / Real.sqrt x) := by
      field_simp [h1]
      <;> nlinarith [h1, Real.sq_sqrt (show 0 ≤ x by linarith)]
    rw [h12]
    rw [h, h10]
    <;> nlinarith
  calc
    x^2 - 1 / x^2 = (x - 1 / x) * (x + 1 / x) := by
      field_simp [h1]
      <;> nlinarith [h1, Real.sq_sqrt (show 0 ≤ x by linarith)]
    _ = (-4 * Real.sqrt 2) * (6) := by
      rw [h11, h5]
    _ = -24 * Real.sqrt 2 := by
      ring_nf