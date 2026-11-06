import Mathlib

theorem algebra_8120 {a : ℝ} (ha : 0 < a ∧ a < 1) (h : a + 1 / a = 3) : a - 1 / a = -Real.sqrt 5 := by
  have h1 : a ≠ 0 := by
    linarith
  have h2 : a * (1 / a) = 1 := by
    field_simp [h1]
  have h3 : (a - 1 / a) ^ 2 = 5 := by
    have h4 : (a + 1 / a) ^ 2 = 9 := by
      rw [h]
      norm_num
    have h5 : (a + 1 / a) ^ 2 = (a - 1 / a) ^ 2 + 4 := by
      field_simp [h1] at h4 ⊢
      nlinarith [h2]
    nlinarith [h4, h5]
  have h6 : a - 1 / a < 0 := by
    have ha1 : 0 < a := ha.1
    have ha2 : a < 1 := ha.2
    have h7 : 1 / a > 1 := by
      have h8 : a > 0 := by linarith
      have h9 : a < 1 := by linarith
      apply (lt_div_iff' (by linarith)).mpr
      nlinarith
    have h10 : a - 1 / a < 0 := by
      linarith
    linarith
  have h7 : a - 1 / a = -Real.sqrt 5 := by
    have h8 : (a - 1 / a) ^ 2 = 5 := h3
    have h9 : a - 1 / a < 0 := h6
    have h10 : a - 1 / a = -Real.sqrt 5 := by
      have h11 : (a - 1 / a) ^ 2 = 5 := h3
      have h12 : Real.sqrt ((a - 1 / a) ^ 2) = Real.sqrt (5) := by
        rw [h11]
      have h13 : Real.sqrt ((a - 1 / a) ^ 2) = -(a - 1 / a) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_neg h9]
      have h14 : -(a - 1 / a) = Real.sqrt 5 := by
        linarith [h12, h13, Real.sqrt_nonneg 5]
      nlinarith
    exact h10
  exact h7