import Mathlib

theorem algebra_183620 {x y : ℝ} (hx : x^2 + y^2 ≠ 0) (hy : y ≠ 0)
    (h1 : x / Real.sqrt (x^2 + y^2) - 1 / x = 7) (h2 : y / Real.sqrt (x^2 + y^2) + 1 / y = 4) :
    (x, y) = (-13 / 96, 13 / 40) := by
  have hx0 : x ≠ 0 := by
    by_contra h
    rw [h] at h1
    field_simp [hy] at h1
  have hS1 : 0 < Real.sqrt (x^2 + y^2) := by
    have hne : x^2 + y^2 > 0 := by
      by_contra h
      push_neg at h
      have : x^2 + y^2 = 0 := by
        have hx2 : x^2 ≥ 0 := sq_nonneg x
        have hy2 : y^2 ≥ 0 := sq_nonneg y
        nlinarith
      tauto
    have hS1 : Real.sqrt (x^2 + y^2) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    linarith
  have Eq1 : x ^ 2 = Real.sqrt (x^2 + y^2) + 7 * x * Real.sqrt (x^2 + y^2) := by 
    field_simp at h1
    nlinarith [Real.sqrt_nonneg (x^2 + y^2), Real.sq_sqrt (show x^2 + y^2 ≥ 0 by positivity)]
  have Eq2 : y ^ 2 = - Real.sqrt (x^2 + y^2) + 4 * y * Real.sqrt (x^2 + y^2) := by 
    field_simp at h2
    nlinarith [Real.sqrt_nonneg (x^2 + y^2), Real.sq_sqrt (show x^2 + y^2 ≥ 0 by positivity)]
  have Eq3 : Real.sqrt (x^2 + y^2) ^ 2 = x^2 + y^2 := Real.sq_sqrt (show x^2 + y^2 ≥ 0 by positivity)
  have Eq4 : Real.sqrt (x^2 + y^2) = 7 * x + 4 * y := by
    nlinarith [Real.sqrt_nonneg (x^2 + y^2), sq_nonneg (7 * x + 4 * y - Real.sqrt (x^2 + y^2)), sq_nonneg (y), sq_nonneg (x)]
  have Eq5 : x ^ 2 = (7 * x + 4 * y) + 7 * x * (7 * x + 4 * y) := by
    rw [Eq4] at Eq1
    nlinarith
  have Eq6 : -48 * x ^ 2 - 28 * x * y - 7 * x - 4 * y = 0 := by
    nlinarith
  have Eq7 : -7 * x - 4 * y + 28 * x * y + 15 * y ^ 2 = 0 := by
    rw [Eq4] at Eq2
    nlinarith
  have h30 : 48 * (x^2) + 56 * (x * y) + 15 * (y^2) = 0 := by
    nlinarith
  have h10 : (y) ≠ 0 := hy
  have h30 : 48 * (x / y)^2 + 56 * (x / y) + 15 = 0 := by
    have h14 : y ≠ 0 := h10
    have h15 : 48 * (x^2) + 56 * (x * y) + 15 * (y^2) = 0 := by
      nlinarith
    have h17 : 48 * (x^2 / (y^2)) + 56 * (x * y / (y^2)) + 15 * (y^2 / (y^2)) = 0 := by
      have h18 : 48 * (x^2 / (y^2)) + 56 * (x * y / (y^2)) + 15 * (y^2 / (y^2)) = (48 * (x^2) + 56 * (x * y) + 15 * (y^2)) / (y^2) := by 
        field_simp
        all_goals ring
      rw [h18]
      rw [h15]
      field_simp [h10]
    have h19 : 48 * (x^2 / (y^2)) + 56 * (x * y / (y^2)) + 15 * (y^2 / (y^2)) = 48 * (x / y)^2 + 56 * (x / y) + 15 := by
      field_simp
      all_goals ring
    linarith [h17, h19]
  have h20 : (x / y + 5 / 12) * (x / y + 3 / 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h20) with h14 h24
  · -- x/y = -5/12
    have h17 : x = -5 * y / 12 := by
      field_simp at h14
      linarith
    rw [h17] at Eq6
    have h25 : y = 13 / 40 := by
      nlinarith [sq_pos_of_ne_zero hy]
    have h26 : x = -13 / 96 := by
      nlinarith
    simp [h26, h25]
  · -- x/y = -3/4
    have h17 : x = -3 * y / 4 := by
      field_simp at h24
      linarith
    rw [h17] at Eq6 Eq7
    exfalso
    nlinarith [sq_pos_of_ne_zero hy]