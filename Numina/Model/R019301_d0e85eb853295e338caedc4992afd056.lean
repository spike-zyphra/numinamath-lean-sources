import Mathlib

theorem algebra_2767 (x : ℝ) (hx : 2 * x - 6 ≥ 0 ∧ x + 4 ≥ 0) :
    Real.sqrt (2 * x - 6) + Real.sqrt (x + 4) = 5 ↔ x = 5 := by
  constructor
  · -- Assuming $\sqrt{2x - 6} + \sqrt{x + 4} = 5$ prove $x = 5$
    intro h
    have h1 : 2 * x - 6 ≥ 0 := hx.1
    have h2 : x + 4 ≥ 0 := hx.2
    have h3 : Real.sqrt (2 * x - 6) + Real.sqrt (x + 4) = 5 := h
    have h4 : (Real.sqrt (2 * x - 6) + Real.sqrt (x + 4)) ^ 2 = (5 : ℝ) ^ 2 := by
      rw [h3]
    have h5 : (Real.sqrt (2 * x - 6) + Real.sqrt (x + 4)) ^ 2 =
        (Real.sqrt (2 * x - 6)) ^ 2 + (Real.sqrt (x + 4)) ^ 2 + 2 * (Real.sqrt (2 * x - 6) * Real.sqrt (x + 4)) := by
      ring
    have h6 : (Real.sqrt (2 * x - 6)) ^ 2 = (2 * x - 6 : ℝ) := by
      apply Real.sq_sqrt
      linarith
    have h7 : (Real.sqrt (x + 4)) ^ 2 = (x + 4 : ℝ) := by
      apply Real.sq_sqrt
      linarith
    rw [h5, h6, h7] at h4
    have h8 : (5 : ℝ) ^ 2 = 25 := by norm_num
    rw [h8] at h4
    have h9 : 2 * (Real.sqrt (2 * x - 6) * Real.sqrt (x + 4)) = 27 - 3 * x := by
      nlinarith
    have h10 : (Real.sqrt (2 * x - 6) * Real.sqrt (x + 4)) ^ 2 = ((27 - 3 * x) / 2) ^ 2 := by
      nlinarith
    have h11 : (Real.sqrt (2 * x - 6) * Real.sqrt (x + 4)) ^ 2 = (2 * x - 6) * (x + 4) := by
      calc
        (Real.sqrt (2 * x - 6) * Real.sqrt (x + 4)) ^ 2 = (Real.sqrt (2 * x - 6)) ^ 2 * (Real.sqrt (x + 4)) ^ 2 := by
          ring_nf
        _ = (2 * x - 6) * (x + 4) := by
          rw [h6, h7]
          all_goals linarith
    rw [h11] at h10
    have h12 : x ^ 2 - 170 * x + 825 = 0 := by
      nlinarith
    have h13 : (x - 5) * (x - 165) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h13) with h14 h15
    · -- First case, where x - 5 = 0. Then x = 5.
      linarith
    · -- Second case, where x - 165 = 0. Then x = 165, which is extraneous.
      have h165 : x = 165 := by linarith
      rw [h165] at h3
      have h17 : Real.sqrt (2 * (165 : ℝ) - 6) = 18 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h18 : Real.sqrt (165 + 4 : ℝ) = 13 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h17, h18] at h3
      norm_num at h3
  · -- Now prove the converse: If x = 5, then the equation holds.
    intro h
    rw [h]
    have h51 : Real.sqrt (2 * (5 : ℝ) - 6) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h52 : Real.sqrt (5 + 4 : ℝ) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h51, h52]
    all_goals norm_num