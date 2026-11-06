import Mathlib

theorem algebra_252180 (x : ℝ) (hx : 0 ≤ 4 * x + 9 ∧ 0 ≤ 11 * x + 1 ∧ 0 ≤ 7 * x + 4) :
    Real.sqrt (4 * x + 9) - Real.sqrt (11 * x + 1) - Real.sqrt (7 * x + 4) = 0 ↔ x = 0 := by
  constructor
  · -- Forward implication: equation implies x = 0
    intro h
    rcases hx with ⟨h1, h2, h3⟩
    have h4 : Real.sqrt (4 * x + 9) = Real.sqrt (11 * x + 1) + Real.sqrt (7 * x + 4) := by 
      linarith
    have h5 : (Real.sqrt (4 * x + 9)) ^ 2 = (Real.sqrt (11 * x + 1) + Real.sqrt (7 * x + 4)) ^ 2 := by
      rw [h4]
    have h6 : (Real.sqrt (4 * x + 9)) ^ 2 = 4 * x + 9 := by
      rw [Real.sq_sqrt]
      linarith
    have h7 : (Real.sqrt (11 * x + 1) + Real.sqrt (7 * x + 4)) ^ 2 =
      (Real.sqrt (11 * x + 1)) ^ 2 + (Real.sqrt (7 * x + 4)) ^ 2 + 2 * (Real.sqrt (11 * x + 1) * Real.sqrt (7 * x + 4)) := by
        ring
    have h8 : (Real.sqrt (11 * x + 1)) ^ 2 = 11 * x + 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h9 : (Real.sqrt (7 * x + 4)) ^ 2 = 7 * x + 4 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h6, h7, h8, h9] at h5
    have h10 : -14 * x + 4 = 2 * (Real.sqrt (11 * x + 1) * Real.sqrt (7 * x + 4)) := by
      nlinarith
      all_goals nlinarith
    -- Next step: Divide both sides by 2 to get $-7 * x + 2 = Real.sqrt (11 * x + 1) * Real.sqrt (7 * x + 4)$.
    have h11 : (-7 * x + 2) ^ 2 = (Real.sqrt (11 * x + 1) * Real.sqrt (7 * x + 4)) ^ 2 := by
      have h14 : Real.sqrt (11 * x + 1) * Real.sqrt (7 * x + 4) = -7 * x + 2 := by
        nlinarith
      rw [h14]
      all_goals nlinarith
    have h12 : (Real.sqrt (11 * x + 1) * Real.sqrt (7 * x + 4)) ^ 2 = (Real.sqrt (11 * x + 1)) ^ 2 * (Real.sqrt (7 * x + 4)) ^ 2 := by
      ring_nf
    have h13 : (Real.sqrt (11 * x + 1)) ^ 2 = 11 * x + 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h14 : (Real.sqrt (7 * x + 4)) ^ 2 = 7 * x + 4 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h12, h13, h14] at h11
    have h15 : (-7 * x + 2) ^ 2 = (11 * x + 1) * (7 * x + 4) := by
      nlinarith
    -- Next step: simplify to get the final solution.
    have h16 : x * (28 * x + 79) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h16) with
    | inl h17 =>
      linarith
    | inr h18 =>
      nlinarith
  · -- Backward implication: x = 0 implies equation
    intro h
    rw [h]
    have h1 : Real.sqrt (4 * (0 : ℝ) + 9) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (11 * (0 : ℝ) + 1) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (7 * (0 : ℝ) + 4) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num
    all_goals norm_num