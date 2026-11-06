import Mathlib

theorem algebra_167118 (x : ℝ) (hx : x > 0 ∧ x ≠ 1) :
    x^2 * Real.logb x 27 * Real.logb 9 x = x + 4 ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2.
    intro h_eq
    have hx1 : x > 0 := hx.1
    have hx2 : x ≠ 1 := hx.2
    have h1 : Real.logb x 27 = Real.log 27 / Real.log x := by
      field_simp [Real.logb]
    have h2 : Real.logb 9 x = Real.log x / Real.log (9 : ℝ) := by
      field_simp [Real.logb]
    rw [h1, h2] at h_eq
    have h3 : Real.log 27 = 3 * Real.log 3 := by
      calc
        Real.log 27 = Real.log (3 ^ 3 : ℝ) := by norm_num
        _ = 3 * Real.log (3 : ℝ) := by simp [Real.log_pow]
    have h4 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      calc
        Real.log (9 : ℝ) = Real.log (3 ^ 2 : ℝ) := by norm_num
        _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
    have h5 : Real.log x ≠ 0 := by
      have hx2' : x > 0 := hx1
      have hx2'' : x ≠ 1 := hx2
      have h6 : Real.log x ≠ 0 := by
        by_contra h
        have h7 : x = 1 := by
          rw [Real.log_eq_zero] at h
          rcases h with (r | r | r)
          · -- x = 1
            linarith
          · -- x = 1
            linarith
          · -- x = 1
            linarith
        contradiction
      assumption
    have h6 : Real.log 27 / Real.log (9 : ℝ) = 3 / 2 := by
      rw [h3, h4]
      have h7 : Real.log 3 > 0 := by
        apply Real.log_pos
        linarith [show (3 : ℝ) > 1 by norm_num]
      field_simp [h7]
      <;> linarith
    have h7 : x^2 * (Real.log 27 / Real.log x) * (Real.log x / Real.log (9 : ℝ)) =
        x^2 * (Real.log 27 / Real.log (9 : ℝ)) := by
      field_simp [h5]
      <;> ring
    have h8 : x^2 * (Real.log 27 / Real.log (9 : ℝ)) = x + 4 := by
      calc
        x^2 * (Real.log 27 / Real.log (9 : ℝ)) = x^2 * (Real.log 27 / Real.log x) * (Real.log x / Real.log (9 : ℝ)) := by
          rw [h7]
        _ = x + 4 := h_eq
    have h9 : x^2 * (Real.log 27 / Real.log (9 : ℝ)) = x^2 * (3 / 2) := by
      rw [show Real.log 27 / Real.log (9 : ℝ) = 3 / 2 by linarith [h6]]
    rw [h9] at h8
    have h10 : 3 * x^2 - 2 * x - 8 = 0 := by
      nlinarith
    have h11 : (x - 2) * (x + 4 / 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- x - 2 = 0
      linarith
    · -- x + 4/3 = 0
      have h14 : x > 0 := hx1
      nlinarith
  · -- Assume x = 2, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb (2 : ℝ) 27 = Real.log 27 / Real.log (2 : ℝ) := by
      field_simp [Real.logb]
    have h2 : Real.logb (9 : ℝ) (2 : ℝ) = Real.log (2 : ℝ) / Real.log (9 : ℝ) := by
      field_simp [Real.logb]
    rw [h1, h2]
    have h3 : Real.log 27 = 3 * Real.log 3 := by
      calc
        Real.log 27 = Real.log (3 ^ 3 : ℝ) := by norm_num
        _ = 3 * Real.log (3 : ℝ) := by simp [Real.log_pow]
    have h4 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      calc
        Real.log (9 : ℝ) = Real.log (3 ^ 2 : ℝ) := by norm_num
        _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
    rw [h3, h4]
    have h5 : Real.log (3 : ℝ) > 0 := by
      apply Real.log_pos
      norm_num
    have h7 : Real.log (2 : ℝ) > 0 := by
      apply Real.log_pos
      norm_num
    field_simp [show Real.log (2 : ℝ) > 0 by linarith, show Real.log (3 : ℝ) > 0 by linarith]
    <;> ring_nf <;> linarith [Real.log_pos (show (2 : ℝ) > 1 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num)]