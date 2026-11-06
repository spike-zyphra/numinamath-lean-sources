import Mathlib

theorem algebra_3214 (a x : ℝ) (ha : 0 < a ∧ a < 1)
  (h : Real.sqrt x = 1 / Real.sqrt a - Real.sqrt a) :
  Real.sqrt (4 * x + x ^ 2) = 1 / a - a := by
  have h1 : 0 < a := ha.1
  have h2 : a < 1 := ha.2
  have h3 : 0 ≤ x := by
    by_contra h3
    push_neg at h3
    have h4 : Real.sqrt x = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      nlinarith
      all_goals nlinarith
    rw [h4] at h
    have h5 : 0 < Real.sqrt a := by
      apply Real.sqrt_pos.mpr
      linarith
    have h6 : 1 / Real.sqrt a > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    have h7 : Real.sqrt a > 0 := h5
    have h8 : (1 / Real.sqrt a - Real.sqrt a) > 0 := by
      have h9 : 1 / Real.sqrt a > Real.sqrt a := by
        have h10 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (by linarith)
        have h11 : Real.sqrt a > 0 := h5
        have h12 : (1 / Real.sqrt a) * Real.sqrt a = 1 := by
          field_simp [h11]
        nlinarith [h10, sq_nonneg (Real.sqrt a - 1), Real.sqrt_nonneg a]
      nlinarith
    linarith
  have eq1 : Real.sqrt x ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith
  have eq2 : Real.sqrt x = 1 / Real.sqrt a - Real.sqrt a := h
  have eq3 : Real.sqrt x ^ 2 = (1 / Real.sqrt a - Real.sqrt a) ^ 2 := by
    rw [eq2]
  have eq4 : x = (1 / Real.sqrt a - Real.sqrt a) ^ 2 := by
    nlinarith [eq1, eq3]
  have eq5 : Real.sqrt a > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have eq6 : Real.sqrt a * Real.sqrt a = a := by
    rw [Real.mul_self_sqrt]
    linarith
  have eq7 : (1 / Real.sqrt a - Real.sqrt a) ^ 2 = (1 / a) - 2 + a := by
    have h8 : Real.sqrt a * Real.sqrt a = a := eq6
    field_simp [show Real.sqrt a ≠ 0 by linarith]
    <;> nlinarith [eq6, sq_pos_of_pos (show 0 < Real.sqrt a by positivity)]
  have eq8 : x = (1 / a) - 2 + a := by
    rw [eq4, eq7]
  have eq9 : 4 * x + x ^ 2 = (1 / a - a) ^ 2 := by
    rw [eq8]
    field_simp [show a ≠ 0 by linarith]
    <;> nlinarith [sq_pos_of_pos (show 0 < a by linarith)]
  have eq10 : Real.sqrt (4 * x + x ^ 2) = Real.sqrt ((1 / a - a) ^ 2) := by
    rw [eq9]
  have eq11 : Real.sqrt ((1 / a - a) ^ 2) = (1 / a - a) := by
    rw [Real.sqrt_sq]
    have h14 : (1 / a - a) > 0 := by
      have h10 : (1 / a) > a := by
        have h15 : a > 0 := h1
        have h17 : a < 1 := h2
        have h11 : 1 / a > 0 := by positivity
        have h12 : 1 / a * a = 1 := by
          field_simp [h15]
        have h13 : a * a < 1 := by nlinarith
        nlinarith [h11, sq_nonneg (1 - a), h13]
      have h10' : (1 / a - a) > 0 := by linarith
      linarith
    linarith
  rw [eq10, eq11]