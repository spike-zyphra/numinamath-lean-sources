import Mathlib

theorem algebra_252050 (x : ℝ) (hx : 2*x^2+5*x-2 ≥ 0 ∧ 2*x^2+5*x-9 ≥ 0) :
    Real.sqrt (2*x^2+5*x-2) - Real.sqrt (2*x^2+5*x-9) = 1 ↔ x = 2 ∨ x = -9/2 := by
  constructor
  · -- Forward direction: if the equation holds, then $x = 2$ or $x = -9/2$.
    intro h
    rcases hx with ⟨h1, h2⟩
    have h3 : Real.sqrt (2 * x ^ 2 + 5 * x - 2) = 1 + Real.sqrt (2 * x ^ 2 + 5 * x - 9) := by
      linarith
    have h4 : (Real.sqrt (2 * x ^ 2 + 5 * x - 2)) ^ 2 = (1 + Real.sqrt (2 * x ^ 2 + 5 * x - 9)) ^ 2 := by
      rw [h3]
    have h5 : (Real.sqrt (2 * x ^ 2 + 5 * x - 2)) ^ 2 = 2 * x ^ 2 + 5 * x - 2 := by
      apply Real.sq_sqrt
      linarith
    have h6 : (1 + Real.sqrt (2 * x ^ 2 + 5 * x - 9)) ^ 2 = 1 + 2 * Real.sqrt (2 * x ^ 2 + 5 * x - 9) + (Real.sqrt (2 * x ^ 2 + 5 * x - 9) ^ 2) := by
      ring
    rw [h5, h6] at h4
    have h7 : (Real.sqrt (2 * x ^ 2 + 5 * x - 9) ^ 2) = 2 * x ^ 2 + 5 * x - 9 := by
      apply Real.sq_sqrt
      linarith
    rw [h7] at h4
    have h8 : Real.sqrt (2 * x ^ 2 + 5 * x - 9) = 3 := by
      nlinarith
    have h9 : 2 * x ^ 2 + 5 * x - 9 = 9 := by
      calc
        2 * x ^ 2 + 5 * x - 9 = (Real.sqrt (2 * x ^ 2 + 5 * x - 9)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 3 ^ 2 := by
          rw [h8]
        _ = 9 := by
          norm_num
    have h10 : 2 * x ^ 2 + 5 * x - 18 = 0 := by
      linarith
    have h11 : (x - 2) * (x + 9 / 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- Case $x - 2 = 0$, so $x = 2$.
      left
      linarith
    · -- Case $x + 9/2 = 0$, so $x = -9/2$.
      right
      linarith
  · -- Backward: if x=2 or x=-9/2 then the equation is valid.
    rintro (h | h)
    · -- Case x=2
      rw [h]
      have h14 : Real.sqrt (2 * (2 : ℝ) ^ 2 + 5 * (2 : ℝ) - 2) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h15 : Real.sqrt (2 * (2 : ℝ) ^ 2 + 5 * (2 : ℝ) - 9) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h14, h15]
      norm_num
    · -- Case x=-9/2
      rw [h]
      have h16 : Real.sqrt (2 * (-9 / 2 : ℝ) ^ 2 + 5 * (-9 / 2 : ℝ) - 2) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h17 : Real.sqrt (2 * (-9 / 2 : ℝ) ^ 2 + 5 * (-9 / 2 : ℝ) - 9) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h16, h17]
      norm_num