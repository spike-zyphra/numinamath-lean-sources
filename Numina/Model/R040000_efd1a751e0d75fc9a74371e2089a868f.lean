import Mathlib

theorem algebra_323198 {a b : ℝ} (ha : a^2 + 2 * a - 1 = 0) (hb : b^4 - 2 * b^2 - 1 = 0)
    (hne : 1 - a * b^2 ≠ 0) :
    ((a * b^2 + b^2 + 1) / a) ^ 1990 = 1 := by

  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith

  have ha1 : a = -1 + Real.sqrt 2 ∨ a = -1 - Real.sqrt 2 := by
    have h2 : a^2 + 2 * a - 1 = 0 := ha
    have h3 : a^2 + 2 * a - 1 = (a - (-1 + Real.sqrt 2)) * (a - (-1 - Real.sqrt 2)) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h3] at h2
    cases (mul_eq_zero.mp h2) with
    | inl h4 => 
      left
      linarith
    | inr h5 => 
      right
      linarith

  have hb1 : b^2 = 1 + Real.sqrt 2 := by
    have h3 : (b^2) ^ 2 - 2 * (b^2) - 1 = 0 := by
      nlinarith [hb]

    have h4 : (b^2 - (1 + Real.sqrt 2)) * (b^2 - (1 - Real.sqrt 2)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

    cases (mul_eq_zero.mp h4) with
    | inl h5 => 
      linarith
    | inr h6 => 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg b]

  cases ha1 with
  | inl ha2 =>
    -- This leads to $1 - a * b^2 = 0$, which contradicts the given
    have hne1 : (1 - a * b^2) = (0 : ℝ) := by
      rw [show a = -1 + Real.sqrt 2 by linarith [ha2], show b^2 = 1 + Real.sqrt 2 by linarith [hb1]]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    contradiction
  | inr ha2 =>
    -- This leads to $\frac{ab^2 + b^2 + 1}{a} = 1$
    have h4 : (a * b^2 + b^2 + 1) / a = 1 := by
      have h3 : a * b^2 + b^2 + 1 = -1 - Real.sqrt 2 := by
        rw [show b^2 = 1 + Real.sqrt 2 by linarith [hb1]]
        rw [show a = -1 - Real.sqrt 2 by linarith [ha2]]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h3, show a = -1 - Real.sqrt 2 by linarith [ha2]]
      field_simp [(show (-1 - Real.sqrt 2 : ℝ) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      )]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

    rw [h4]
    norm_num