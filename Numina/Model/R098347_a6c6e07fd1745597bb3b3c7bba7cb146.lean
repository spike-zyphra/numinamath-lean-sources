import Mathlib

theorem algebra_185413 {a : ℝ} (P : ℝ → ℝ)
    (hP : P = fun x => a^3 * x^5 + (1 - a) * x^4 + (1 + a^3) * x^2 + (1 - 3 * a) * x - a^3) :
    (P 1 = 0) ↔ (a = 1 ∨ a = (-1 - Real.sqrt 13) / 2 ∨ a = (-1 + Real.sqrt 13) / 2) := by
  have h1 : P 1 = a^3 * 1^5 + (1 - a) * 1^4 + (1 + a^3) * 1^2 + (1 - 3 * a) * 1 - a^3 := by rw [hP]
  have eq1 : P 1 = a^3 + 3 - 4 * a := by
    rw [h1]
    ring
  rw [eq1]
  constructor
  · -- Forward direction: If $P(1) = 0$ then $a = 1$ or $a = \frac{-1 ± \sqrt{13}}{2}$
    intro h
    have h_eq : a^3 + 3 - 4 * a = 0 := by linarith
    have h_eq2 : a^3 - 4 * a + 3 = 0 := by linarith
    have h_eq3 : (a - 1) * (a^2 + a - 3) = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1/2), Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
    · -- Case $a - 1 = 0$, so $a = 1$
      left
      have h_eq6 : a = 1 := by linarith
      exact h_eq6
    · -- Case $a^2 + a - 3 = 0$, solve using the quadratic formula
      have h_eq6 : a^2 + a - 3 = 0 := by linarith
      have h_eq7 : (a - (-1 - Real.sqrt 13) / 2) * (a - (-1 + Real.sqrt 13) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h_eq7) with h_eq8 h_eq9
      · -- Case $a = \frac{-1 - \sqrt{13}}{2}$
        right
        left
        have ha2 : a = (-1 - Real.sqrt 13) / 2 := by linarith
        exact ha2
      · -- Case $a = \frac{-1 + \sqrt{13}}{2}$
        right
        right
        have ha3 : a = (-1 + Real.sqrt 13) / 2 := by linarith
        exact ha3
  · -- Backward direction: If $a = 1$, $\frac{-1 ± \sqrt{13}}{2}$ then $P(1) = 0$
    rintro (ha | ha | ha)
    · -- Case $a = 1$
      rw [ha]
      norm_num
    · -- Case $a = \frac{-1 - \sqrt{13}}{2}$
      rw [ha]
      nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num)]
    · -- Case $a = \frac{-1 + \sqrt{13}}{2}$
      rw [ha]
      nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num)]