import Mathlib

theorem algebra_283710 :
    {x : ℝ | x ^ 2 - 3.5 * x + 2 ≥ 0 ∧ 4 * x ^ 2 + Real.sqrt (x ^ 2 - 3.5 * x + 2) = 14 * x + 10} = {4, -1/2} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, 
    Set.union_singleton]
  constructor
  · -- First, show that if x in the left side, then x in the right side
    rintro ⟨hx1, heq⟩
    have h1 : Real.sqrt (x ^ 2 - 3.5 * x + 2) ≥ 0 := by 
      apply Real.sqrt_nonneg
    have h2 : (Real.sqrt (x ^ 2 - 3.5 * x + 2)) ^ 2 = x^2 - 3.5 * x + 2 := by
      rw [Real.sq_sqrt]
      linarith
    have heq2 : 4 * x^2 + Real.sqrt (x ^ 2 - 3.5 * x + 2) = 14 * x + 10 := by
      linarith [heq]
    have h3 : (14 * x + 10 - 4 * x^2) ^2 = x^2 - 3.5 * x + 2 := by 
      nlinarith [h2, heq2, Real.sqrt_nonneg (x ^ 2 - 3.5 * x + 2)]
    have h4 : (x - 4) * (x + 1/2) = 0 := by
      ring_nf at h3
      nlinarith [sq_nonneg (x ^ 2 - 2 * x * (4 : ℝ) ), sq_nonneg (x * (x -4)), sq_nonneg ((14 * x + 10 - 4 * x^2) + (x -4)), sq_nonneg ((x + 1/2) * (x -4)), sq_nonneg (x^2 - (x) * (x + 1/2) / (1 : ℝ))]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- x = 4 
      left 
      linarith 
    · -- x = -1/2 
      right 
      linarith 
  · -- Now the reverse 
    rintro (h | h)
    · -- x = 4 
      rw [h] 
      constructor
      · norm_num 
      · -- Check the equation 
        have h3 : Real.sqrt (4 ^ 2 - 3.5 * (4 : ℝ) + 2) = 2 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h3] 
        all_goals norm_num 
    · -- x = -1/2 
      rw [h] 
      constructor 
      · norm_num 
      · -- Check the equation 
        have h3 : Real.sqrt ((-1/2 : ℝ) ^ 2 - 3.5 * (-1/2) + 2) = 2 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h3] 
        all_goals norm_num