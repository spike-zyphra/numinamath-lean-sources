import Mathlib

theorem algebra_307691 {a : ℝ} (ha : a = (Real.sqrt 5 - 1) / 2) :
    (a^5 + a^4 - 2 * a^3 - a^2 - a + 2) / (a^3 - a) = -2 := by

  have ha2 : a^2 + a - 1 = 0 := by
    rw [ha]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have ha2' : a^2 = 1 - a := by
    linarith
  have h1 : a^3 = 2 * a - 1 := by
    calc
      a^3 = a * a^2 := by ring
      _   = a * (1 - a) := by rw [show a^2 = 1 - a by linarith [ha2]]
      _   = a - a^2 := by ring
      _   = a - (1 - a) := by rw [show a^2 = 1 - a by linarith [ha2]]
      _   = 2 * a - 1 := by ring

  have h2 : a^4 = 2 - 3 * a := by
    calc
      a^4 = a * a^3 := by ring
      _   = a * (2 * a - 1) := by rw [h1]
      _   = 2 * a^2 - a := by ring
      _   = 2 * (1 - a) - a := by rw [show a^2 = 1 - a by linarith [ha2]]
      _   = 2 - 3 * a := by ring

  have h3 : a^5 = 5 * a - 3 := by
    calc
      a^5 = a * a^4 := by ring
      _   = a * (2 - 3 * a) := by rw [h2]
      _   = 2 * a - 3 * a^2 := by ring
      _   = 2 * a - 3 * (1 - a) := by rw [show a^2 = 1 - a by linarith [ha2]]
      _   = 5 * a - 3 := by ring

  have h4 : a^3 - a = a - 1 := by
    rw [h1]
    nlinarith

  have h5 : a^5 + a^4 - 2 * a^3 - a^2 - a + 2 = 2 - 2 * a := by
    rw [h3, h2, h1, show a^2 = 1 - a by linarith [ha2]]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), ha2]

  have h7 : a - 1 ≠ 0 := by
    rw [ha]
    -- Show that (Real.sqrt 5 - 1) / 2 - 1 ≠ 0
    have h1 : Real.sqrt 5 > 1 := by
      have h2 : Real.sqrt 5 > Real.sqrt 1 := by
        apply Real.sqrt_lt_sqrt
        norm_num
        norm_num
      have h3 : Real.sqrt 1 = 1 := Real.sqrt_one
      linarith
    have h4 : Real.sqrt 5 < 3 := by
      have h5 : Real.sqrt 5 < Real.sqrt 9 := by
        apply Real.sqrt_lt_sqrt
        norm_num
        norm_num
      have h6 : Real.sqrt 9 = 3 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      linarith [h5, h6]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

  have h6 : (a^5 + a^4 - 2 * a^3 - a^2 - a + 2) / (a^3 - a) = (2 - 2 * a) / (a - 1) := by
    have num_eq : a^5 + a^4 - 2 * a^3 - a^2 - a + 2 = 2 - 2 * a := by
      nlinarith [h5]
    have denom_eq : a^3 - a = a - 1 := by
      nlinarith [h4]
    rw [num_eq, denom_eq]

  rw [h6]
  field_simp [h7]
  <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), ha2]