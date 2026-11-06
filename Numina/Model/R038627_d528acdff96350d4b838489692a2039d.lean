import Mathlib

theorem algebra_261353 :
  {x : ℝ | -1/5 ≤ x ∧ Real.sqrt (2 * x + 3) + Real.sqrt (5 * x + 1) = Real.sqrt (12 * x + 13)} = {3} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if $x$ is in the set, then $x = 3$.
    rintro ⟨hx1, heq⟩
    have h1 : Real.sqrt (2 * x + 3) + Real.sqrt (5 * x + 1) = Real.sqrt (12 * x + 13) := heq
    have h2 : (Real.sqrt (2 * x + 3) + Real.sqrt (5 * x + 1)) ^ 2 = (Real.sqrt (12 * x + 13)) ^ 2 := by
      rw [h1]
    have h3 : (Real.sqrt (2 * x + 3) + Real.sqrt (5 * x + 1)) ^ 2 = (Real.sqrt (2 * x + 3)) ^ 2 + (Real.sqrt (5 * x + 1)) ^ 2 + 2 * (Real.sqrt (2 * x + 3) * Real.sqrt (5 * x + 1)) := by ring
    have h4 : (Real.sqrt (12 * x + 13)) ^ 2 = 12 * x + 13 := by
      apply Real.sq_sqrt
      linarith
    have h5 : (Real.sqrt (2 * x + 3)) ^ 2 = 2 * x + 3 := by
      apply Real.sq_sqrt
      linarith
    have h6 : (Real.sqrt (5 * x + 1)) ^ 2 = 5 * x + 1 := by
      apply Real.sq_sqrt
      linarith
    rw [h3] at h2
    rw [h4, h5, h6] at h2
    have h7 : 2 * (Real.sqrt (2 * x + 3) * Real.sqrt (5 * x + 1)) = 5 * x + 9 := by
      nlinarith
    have h8 : (Real.sqrt (2 * x + 3) * Real.sqrt (5 * x + 1)) ^ 2 = ((5 * x + 9) / 2) ^ 2 := by
      have h9 : Real.sqrt (2 * x + 3) * Real.sqrt (5 * x + 1) = (5 * x + 9) / 2 := by
        nlinarith [Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (5 * x + 1)]
      rw [h9]
    have h9 : (Real.sqrt (2 * x + 3) * Real.sqrt (5 * x + 1)) ^ 2 = (2 * x + 3) * (5 * x + 1) := by
      calc
        (Real.sqrt (2 * x + 3) * Real.sqrt (5 * x + 1)) ^ 2
          = (Real.sqrt (2 * x + 3)) ^ 2 * (Real.sqrt (5 * x + 1)) ^ 2 := by rw [mul_pow]
        _ = (2 * x + 3) * (5 * x + 1) := by
          rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    rw [h9] at h8
    have h10 : 15 * x ^ 2 - 22 * x - 69 = 0 := by
      nlinarith
    have h11 : (x - 3) * (x + 23 / 15) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- Case where $x - 3 = 0$
      linarith
    · -- Case where $x + \frac{23}{15} = 0$
      have h14 : x < -1 / 5 := by
        nlinarith
      linarith
  · -- Now, prove the converse: if x = 3, then it's in the set
    intro h
    rw [h]
    constructor
    · norm_num
    · -- Show that sqrt(2x+3) + sqrt(5x+1) = sqrt(12x+13) when x = 3
      have h15 : Real.sqrt (2 * (3 : ℝ) + 3) + Real.sqrt (5 * (3 : ℝ) + 1) = Real.sqrt (12 * (3 : ℝ) + 13) := by
        have h1 : Real.sqrt (2 * (3 : ℝ) + 3) = (3 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h2 : Real.sqrt (5 * (3 : ℝ) + 1) = (4 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h3 : Real.sqrt (12 * (3 : ℝ) + 13) = (7 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h1, h2, h3]
        all_goals norm_num
      exact h15