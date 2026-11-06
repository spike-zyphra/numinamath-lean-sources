import Mathlib

theorem algebra_320388 {a b : ℝ} (ha : 3 * a ^ 4 + 2 * a ^ 2 - 4 = 0) (hb : b ^ 4 + b ^ 2 - 3 = 0) :
    4 / a ^ 4 + b ^ 4 = 7 := by

  have ha2_ne_zero : a ^ 2 ≠ 0 := by
    by_contra h
    have h1 : a ^ 2 = 0 := by linarith
    have h2 : 3 * a ^ 4 + 2 * a ^ 2 - 4 = 0 := ha
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring] at h2
    rw [h1] at h2
    nlinarith

  have ha4_ne_zero : a ^ 4 ≠ 0 := by
    have ha2 : a ^ 2 ≠ 0 := ha2_ne_zero
    have h : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [h]
    exact pow_ne_zero 2 ha2

  have h1 : 3 * (a ^ 2) ^ 2 + 2 * (a ^ 2) - 4 = 0 := by
    have h : 3 * a ^ 4 + 2 * a ^ 2 - 4 = 0 := ha
    have h2 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [h2] at h
    linarith

  have h2 : (b ^ 2) ^ 2 + (b ^ 2) - 3 = 0 := by
    have h : b ^ 4 + b ^ 2 - 3 = 0 := hb
    have h2 : b ^ 4 = (b ^ 2) ^ 2 := by ring
    rw [h2] at h
    linarith

  have h3 : a ^ 2 = (-1 + Real.sqrt 13) / 3 := by
    have h14 : 3 * (a ^ 2) ^ 2 + 2 * (a ^ 2) - 4 = 0 := h1
    have h5 : 3 * (a ^ 2) ^ 2 + 2 * (a ^ 2) - 4 = 3 * ((a ^ 2) - (-1 + Real.sqrt 13) / 3) * ((a ^ 2) - (-1 - Real.sqrt 13) / 3) := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 13 by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num : (0 : ℝ) ≤ 13)]
    rw [h5] at h14
    cases (mul_eq_zero.mp h14) with
    | inl h6 =>
      have h7 : (a ^ 2) = (-1 + Real.sqrt 13) / 3 := by
        nlinarith
      exact h7
    | inr h8 =>
      have h9 : (a ^ 2) = (-1 - Real.sqrt 13) / 3 := by
        nlinarith
      have h10 : Real.sqrt 13 > 0 := by
        positivity
      have h11 : (-1 - Real.sqrt 13) / 3 < 0 := by
        nlinarith
      have h12 : a ^ 2 ≥ 0 := by
        positivity
      linarith

  have h38 : a ^ 4 = (14 - 2 * Real.sqrt 13) / 9 := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = ((-1 + Real.sqrt 13) / 3) ^ 2 := by rw [h3]
      _ = (14 - 2 * Real.sqrt 13) / 9 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < 13 by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num : (0 : ℝ) ≤ 13)]

  have h39 : 4 / a ^ 4 = (7 + Real.sqrt 13) / 2 := by
    rw [h38]
    have h11 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)
    field_simp [(show (14 - 2 * Real.sqrt 13 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    )]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]

  have h4 : b ^ 2 = (-1 + Real.sqrt 13) / 2 := by
    have h13 : (b ^ 2) ^ 2 + (b ^ 2) - 3 = 0 := h2
    have h5 : (b ^ 2) ^ 2 + (b ^ 2) - 3 = ((b ^ 2) - (-1 + Real.sqrt 13) / 2) * ((b ^ 2) - (-1 - Real.sqrt 13) / 2) := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 13 by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num : (0 : ℝ) ≤ 13)]
    rw [h5] at h13
    cases (mul_eq_zero.mp h13) with
    | inl h6 =>
      have h7 : (b ^ 2) = (-1 + Real.sqrt 13) / 2 := by
        nlinarith
      exact h7
    | inr h8 =>
      have h9 : (b ^ 2) = (-1 - Real.sqrt 13) / 2 := by
        nlinarith
      have h10 : Real.sqrt 13 > 0 := by
        positivity
      have h11 : (-1 - Real.sqrt 13) / 2 < 0 := by
        nlinarith
      have h12 : b ^ 2 ≥ 0 := by
        positivity
      linarith

  have h44 : b ^ 4 = (7 - Real.sqrt 13) / 2 := by
    calc
      b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ = ((-1 + Real.sqrt 13) / 2) ^ 2 := by rw [h4]
      _ = (7 - Real.sqrt 13) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < 13 by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num : (0 : ℝ) ≤ 13)]

  linarith [h39, h44]