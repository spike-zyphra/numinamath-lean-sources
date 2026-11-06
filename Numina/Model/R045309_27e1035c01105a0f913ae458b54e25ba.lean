import Mathlib

theorem algebra_219331 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 1) (h2 : y^2 + z^2 + y * z = 2) (h3 : z^2 + x^2 + z * x = 3) :
    x + y + z = Real.sqrt (3 + Real.sqrt 6) := by

  have eq4 : (z - x) * (x + y + z) = 1 := by
    nlinarith
  have eq5 : (x - y) * (x + y + z) = 1 := by
    nlinarith
  have h4 : y + z = 2 * x := by
    have h_eq : (z - x) * (x + y + z) = (x - y) * (x + y + z) := by
      nlinarith
    have h5 : x + y + z > 0 := by
      positivity
    have h7 : z - x = x - y := by
      apply (mul_left_inj' (ne_of_gt h5)).mp
      nlinarith
    linarith
  have h5 : x + y + z = 3 * x := by
    linarith [h4]

  have h5' : 27 * x^4 - 18 * x^2 + 1 = 0 := by
    have eq1 : 3 * x * (z - x) = 1 := by
      have h8 : (z - x) * (3 * x) = 1 := by
        have h9 : (z - x) * (x + y + z) = 1 := by
          nlinarith
        have h10 : x + y + z = 3 * x := by
          linarith [h4]
        rw [h10] at h9
        linarith
      nlinarith
    have h11 : z = x + 1 / (3 * x) := by
      field_simp at eq1 ⊢
      nlinarith
    have h12 : z^2 + x^2 + x * z = 3 := by
      nlinarith [h3]
    rw [show z = x + 1 / (3 * x) by linarith [h11]] at h12
    field_simp at h12
    nlinarith [sq_pos_of_pos hx]

  have h6 : x^2 = (3 + Real.sqrt 6) / 9 := by
    have h7 : 27 * x^4 - 18 * x^2 + 1 = 0 := h5'
    have h8 : 27 * x^4 - 18 * x^2 + 1 = 27 * (x^2) ^ 2 - 18 * (x^2) + 1 := by ring
    rw [h8] at h7
    have h10 : (x^2 - (3 + Real.sqrt 6) / 9) * (x^2 - (3 - Real.sqrt 6) / 9) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (0 : ℝ) < 6), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 h10) with h11 h12
    · linarith
    · have h13 : x^2 = (3 - Real.sqrt 6) / 9 := by linarith
      have h14 : Real.sqrt 6 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      have h15 : x^2 < 1 / 3 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      nlinarith [sq_nonneg (y - (x - 1 / (3 * x))), h1, h13, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]

  have h7 : (x + y + z) ^ 2 = 3 + Real.sqrt 6 := by
    have h10 : x + y + z = 3 * x := by
      linarith [h4]
    rw [h10]
    calc
      (3 * x) ^ 2 = 9 * x^2 := by ring
      _ = 9 * ((3 + Real.sqrt 6) / 9) := by
        rw [show x^2 = (3 + Real.sqrt 6) / 9 by linarith [h6]]
      _ = (3 + Real.sqrt 6) := by
        ring

  have h8 : x + y + z ≥ 0 := by
    positivity

  have h9 : x + y + z = Real.sqrt ((x + y + z) ^ 2) := by
    rw [Real.sqrt_sq (show 0 ≤ x + y + z by linarith [h8])]

  rw [h9]
  rw [h7]