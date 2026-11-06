import Mathlib

theorem algebra_185484 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a + b = 6) (h2 : 1 / a + 1 / b = 6) :
    (a, b) = (3 + 2 * Real.sqrt 2, 3 - 2 * Real.sqrt 2) ∨
    (a, b) = (3 - 2 * Real.sqrt 2, 3 + 2 * Real.sqrt 2) := by
  have h3 : b = 6 - a := by linarith
  rw [h3] at h2
  have h4 : a * (6 - a) ≠ 0 := by
    apply mul_ne_zero
    exact ha
    -- Now need to show that (6 - a) ≠ 0
    by_contra h
    have h5 : 6 - a = 0 := by
      nlinarith
    have h6 : a = 6 := by linarith
    have h7 : b = 0 := by nlinarith [h3, h6]
    contradiction
  have h9 : a * (6 - a) * (1 / a + 1 / (6 - a)) = 6 := by
    have h10 : a * (6 - a) * (1 / a) = (6 - a) := by
      field_simp [show a ≠ 0 by exact ha, show (6 - a) ≠ 0 by 
        by_contra h
        have h6 : a = 6 := by nlinarith
        have h7 : b = 0 := by nlinarith [h3, h6]
        contradiction
      ]
      <;> ring_nf <;> tauto
    have h11 : a * (6 - a) * (1 / (6 - a)) = a := by
      have h5 : 6 - a ≠ 0 := by
        by_contra h
        have h6 : a = 6 := by nlinarith
        have h7 : b = 0 := by nlinarith [h3, h6]
        contradiction
      field_simp [h5]
      <;> ring_nf <;> tauto
    calc
      a * (6 - a) * (1 / a + 1 / (6 - a)) = a * (6 - a) * (1 / a) + a * (6 - a) * (1 / (6 - a)) := by ring
      _ = (6 - a) + a := by rw [h10, h11]
      _ = 6 := by linarith
  have h5 : a^2 - 6 * a + 1 = 0 := by
    nlinarith [h2, h9]
  have h6 : a = 3 + 2 * Real.sqrt 2 ∨ a = 3 - 2 * Real.sqrt 2 := by
    have h7 : a^2 - 6 * a + 1 = 0 := h5
    have h8 : (a - (3 + 2 * Real.sqrt 2)) * (a - (3 - 2 * Real.sqrt 2)) = 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (a - 3)]
    cases (mul_eq_zero.mp h8) with
    | inl h9 =>
      left
      linarith
    | inr h10 =>
      right
      linarith
  cases h6 with
  | inl ha1 =>
    have hb1 : b = 3 - 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    left
    exact Prod.ext ha1 hb1
  | inr ha2 =>
    have hb2 : b = 3 + 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    right
    exact Prod.ext ha2 hb2