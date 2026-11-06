import Mathlib

theorem algebra_10587 : {c : ℝ | Real.sqrt (4 + Real.sqrt (8 + 4 * c)) + Real.sqrt (2 + Real.sqrt (2 + c)) = 2 + 2 * Real.sqrt 2 ∧ 8 + 4*c ≥ 0 ∧ 2 + c ≥ 0} = {2} := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward implication: if c satisfies the equation and constraints, then c = 2
    intro h
    rcases h with ⟨h_eq, h1, h2⟩
    have h3 : Real.sqrt (8 + 4 * c) = 2 * Real.sqrt (2 + c) := by
      have h4 : Real.sqrt (8 + 4 * c) = Real.sqrt (4 * (2 + c)) := by ring_nf
      rw [h4]
      have h5 : Real.sqrt (4 * (2 + c)) = Real.sqrt (4 : ℝ) * Real.sqrt ((2 + c) : ℝ) := by
        rw [Real.sqrt_mul (by
          nlinarith
        )]
      rw [h5]
      have h6 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h6]
    have h7 : Real.sqrt (4 + Real.sqrt (8 + 4 * c)) = Real.sqrt 2 * Real.sqrt (2 + Real.sqrt (2 + c)) := by
      have h33 : Real.sqrt (8 + 4 * c) = 2 * Real.sqrt (2 + c) := h3
      have h8 : 4 + Real.sqrt (8 + 4 * c) = 2 * (2 + Real.sqrt (2 + c)) := by
        rw [h33]
        nlinarith [Real.sqrt_nonneg (2 + c)]
      have h9 : Real.sqrt (4 + Real.sqrt (8 + 4 * c)) = Real.sqrt (2 * (2 + Real.sqrt (2 + c)) ) := by
        rw [h8]
      rw [h9]
      have h10 : Real.sqrt (2 * (2 + Real.sqrt (2 + c)) ) = Real.sqrt 2 * Real.sqrt (2 + Real.sqrt (2 + c)) := by
        rw [Real.sqrt_mul (by positivity)]
      rw [h10]
    have h11 : Real.sqrt (4 + Real.sqrt (8 + 4 * c)) + Real.sqrt (2 + Real.sqrt (2 + c)) = 2 + 2 * Real.sqrt 2 := h_eq
    rw [h7] at h11
    have h13 : Real.sqrt (2 + Real.sqrt (2 + c)) = 2 := by
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt (2 + c)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + Real.sqrt (2 + c)) by positivity)]
    have h14 : Real.sqrt (2 + c) = 2 := by
      have h14 : Real.sqrt (2 + Real.sqrt (2 + c)) = 2 := h13
      have h15 : 2 + Real.sqrt (2 + c) ≥ 0 := by positivity
      have h16 : Real.sqrt (2 + Real.sqrt (2 + c)) ^ 2 = (2 : ℝ) ^ 2 := by
        rw [h14]
      have h17 : Real.sqrt (2 + Real.sqrt (2 + c)) ^ 2 = 2 + Real.sqrt (2 + c) := by
        rw [Real.sq_sqrt]
        positivity
      have h18 : Real.sqrt (2 + c) = 2 := by
        nlinarith [Real.sqrt_nonneg (2 + c)]
      exact h18
    have h18 : 2 + c = 4 := by
      have h19 : Real.sqrt (2 + c) = 2 := h14
      have h20 : Real.sqrt (2 + c) ^ 2 = (2 : ℝ) ^ 2 := by
        rw [h19]
      have h21 : Real.sqrt (2 + c) ^ 2 = 2 + c := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith
    linarith
  · -- Backward implication: if c = 2, then it satisfies the equation and constraints
    intro h
    rw [h]
    constructor
    · -- Check the equation
      have h3 : Real.sqrt (4 + Real.sqrt (8 + 4 * (2 : ℝ))) + Real.sqrt (2 + Real.sqrt (2 + (2 : ℝ))) = 2 + 2 * Real.sqrt 2 := by
        have h4 : Real.sqrt (8 + 4 * (2 : ℝ)) = 4 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        have h5 : Real.sqrt (4 + Real.sqrt (8 + 4 * (2 : ℝ))) = Real.sqrt 8 := by
          rw [h4]
          all_goals norm_num
        have h6 : Real.sqrt (2 + Real.sqrt (2 + (2 : ℝ))) = (2 : ℝ) := by
          have h7 : Real.sqrt (2 + (2 : ℝ)) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          have h8 : 2 + Real.sqrt (2 + (2 : ℝ)) = (4 : ℝ) := by
            rw [h7]
            all_goals norm_num
          rw [h8]
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        rw [h5, h6]
        have h9 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h9]
        all_goals nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith
    constructor
    · -- Check 8 + 4 * 2 ≥ 0
      norm_num
    · -- Check 2 + 2 ≥ 0
      norm_num