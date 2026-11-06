import Mathlib

theorem algebra_206615 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + b^2 - c^2 = √3 * a * b) (h2 : a^2 - b^2 + c^2 = √2 * a * c) :
    b / c = √2 := by

  have h_eq1 : 2 * a = √3 * b + √2 * c := by
    have h3 : 2 * a^2 = √3 * a * b + √2 * a * c := by
      nlinarith
    have ha_pos : a ≠ 0 := by linarith
    apply (mul_left_inj' ha_pos).mp
    linarith

  have h_eq2 : √3 * a * b + c^2 - b^2 = √2 * a * c + b^2 - c^2 := by
    have h3 : a^2 + b^2 - c^2 = √3 * a * b := by linarith
    have h4 : a^2 - b^2 + c^2 = √2 * a * c := by linarith
    nlinarith

  have eq_a : a = (√3 * b + √2 * c) / 2 := by
    have : a = (√3 * b + √2 * c) / 2 := by
      linarith
    linarith

  rw [eq_a] at h_eq2

  have h_eq3 : b ^ 2 = 2 * c ^ 2 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]

  have h_eq4 : b ^ 2 = 2 * c ^ 2 := h_eq3

  have h_eq5 : b = Real.sqrt 2 * c := by
    have h3 : c > 0 := by assumption
    have h4 : b ^ 2 - 2 * c ^ 2 = 0 := by linarith
    have h_eq6 : (b - Real.sqrt 2 * c) * (b + Real.sqrt 2 * c) = 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h_eq6) with h_eq7 h_eq8
    · -- case $b - \sqrt{2}c = 0$
      linarith
    · -- case $b + \sqrt{2}c = 0$
      have h_eq9 : b + Real.sqrt 2 * c = 0 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), mul_pos (show 0 < (2 : ℝ) by norm_num) (show 0 < c by linarith)]

  have : b / c = Real.sqrt 2 := by
    have c_pos : c ≠ 0 := by linarith
    field_simp at *
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]

  exact this