import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_242351 :
  {(a, b) : ℝ × ℝ | ∃ x y, x^2 + y^2 = a^2 ∧ x + y = b} =
  {(a, b) : ℝ × ℝ | |b| ≤ sqrt 2 * |a|} := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume that there's a solution
    rintro ⟨x, y, h1, h2⟩
    have h3 : y = b - x := by linarith
    rw [h3] at h1
    have h4 : 2 * x ^ 2 - 2 * b * x + (b ^ 2 - a ^ 2) = 0 := by
      nlinarith [h1]
    have h5 : (-2 * b) ^ 2 - 4 * (2) * (b ^ 2 - a ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (2 * x - b)]
    have h6 : 2 * a ^ 2 ≥ b ^ 2 := by
      nlinarith
    have h7 : |b| ≤ Real.sqrt 2 * |a| := by
      have h6 : b ^ 2 ≤ 2 * a ^ 2 := by
        nlinarith
      have h9 : b ^ 2 ≤ 2 * a ^ 2 := by linarith
      have h10 : |b| ≥ 0 := by apply abs_nonneg
      have h11 : Real.sqrt 2 * |a| ≥ 0 := by
        have h12 : Real.sqrt 2 ≥ 0 := by positivity
        have h13 : |a| ≥ 0 := by apply abs_nonneg
        nlinarith
      have h13 : Real.sqrt (b ^ 2) ≤ Real.sqrt (2 * a ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h14 : Real.sqrt (b ^ 2) = |b| := by
        rw [Real.sqrt_sq_eq_abs]
      have h15 : Real.sqrt (2 * a ^ 2) = Real.sqrt 2 * |a| := by
        calc
          Real.sqrt (2 * a ^ 2) = Real.sqrt (2 * (a ^ 2)) := by ring_nf
          _ = Real.sqrt (2) * Real.sqrt (a ^ 2) := by 
            rw [Real.sqrt_mul (by positivity)]
          _ = Real.sqrt 2 * (|a|) := by
            have h100 : Real.sqrt (a ^ 2) = |a| := by 
              rw [Real.sqrt_sq_eq_abs]
            rw [h100]
            all_goals ring
      linarith [h14, h15, h13]
    simpa using h7
  · -- Assume |b| ≤ sqrt 2 * |a|, prove existence of solution
    intro h
    have h1 : b ^ 2 ≤ 2 * a ^ 2 := by
      have h2 : |b| ≤ Real.sqrt 2 * |a| := by
        simpa using h
      have h3 : |b| ≥ 0 := by positivity
      have h4 : Real.sqrt 2 * |a| ≥ 0 := by positivity
      have h5 : |b| ^ 2 ≤ (Real.sqrt 2 * |a|) ^ 2 := by
        nlinarith [h2, abs_nonneg (b), mul_nonneg (Real.sqrt_nonneg 2) (abs_nonneg a)]
      have h6 : (Real.sqrt 2 * |a|) ^ 2 = 2 * a ^ 2 := by
        calc
          (Real.sqrt 2 * |a|) ^ 2 = (Real.sqrt 2) ^ 2 * (|a|) ^ 2 := by ring
          _ = (2) * (|a|) ^ 2 := by 
            rw [Real.sq_sqrt]
            all_goals norm_num
          _ = 2 * |a| ^ 2 := by ring
          _ = 2 * a ^ 2 := by
            rw [sq_abs]
      have h7 : |b| ^ 2 = b ^ 2 := by
        rw [sq_abs]
      nlinarith [h5, h7, h6]
    have h2 : 2 * a ^ 2 - b ^ 2 ≥ 0 := by
      linarith
    use (b + Real.sqrt (2 * a ^ 2 - b ^ 2)) / 2,
      (b - Real.sqrt (2 * a ^ 2 - b ^ 2)) / 2
    constructor
    · -- Check x^2 + y^2 = a^2
      nlinarith [Real.sqrt_nonneg (2 * a ^ 2 - b ^ 2), Real.sq_sqrt (show (2 * a ^ 2 - b ^ 2) ≥ 0 by linarith)]
    · -- Check x + y = b
      ring_nf