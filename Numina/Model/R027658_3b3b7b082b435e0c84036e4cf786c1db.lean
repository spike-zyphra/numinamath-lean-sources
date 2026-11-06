import Mathlib

theorem algebra_2381 :
  {x : ℝ | x ∈ Set.Icc (-2) (22 / 3) ∧ 4 * √(x + 2) + √(22 - 3 * x) = x ^ 2 + 8} = {-1, 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Forward: if x is in the set, then x = -1 or x = 2
    rintro ⟨⟨hx1, hx2⟩, heq⟩
    have h1 : Real.sqrt (x + 2) ≥ 0 := Real.sqrt_nonneg (x + 2)
    have h2 : Real.sqrt (22 - 3 * x) ≥ 0 := Real.sqrt_nonneg (22 - 3 * x)
    have h5 : Real.sqrt (x + 2) ^ 2 = x + 2 := by
      apply Real.sq_sqrt
      linarith
    have h6 : Real.sqrt (22 - 3 * x) ^ 2 = 22 - 3 * x := by
      apply Real.sq_sqrt
      nlinarith
    have h9 : Real.sqrt (22 - 3 * x) ≥ 0 := Real.sqrt_nonneg (22 - 3 * x)
    have h11 : x + 2 ≥ 0 := by linarith
    have h16 : (x - (-1)) * (x - 2) = 0 := by
      nlinarith [Real.sqrt_nonneg (x + 2), 
        Real.sqrt_nonneg (22 - 3 * x), 
        sq_nonneg (Real.sqrt (x + 2) - 1), 
        sq_nonneg (Real.sqrt (x + 2) - 2), 
        sq_nonneg (Real.sqrt (22 - 3 * x) - 5), 
        sq_nonneg (Real.sqrt (22 - 3 * x) - 4), 
        Real.sq_sqrt (show x + 2 ≥ 0 by linarith), 
        Real.sq_sqrt (show 22 - 3 * x ≥ 0 by nlinarith), 
        Real.sq_sqrt (show (22 - 3 * x) ≥ 0 by nlinarith), 
        sq_nonneg (x - 2), 
        sq_nonneg (x + 1), 
        heq, 
        mul_nonneg (Real.sqrt_nonneg (x + 2)) (Real.sqrt_nonneg (22 - 3 * x))
      ]
    cases' (mul_eq_zero.mp h16) with h7 h8
    · -- Case where x = -1
      left
      linarith
    · -- Case where x = 2
      right
      linarith
  · -- Reverse: if x = -1 or x = 2, then x is in the set
    rintro (rfl | rfl)
    · -- Case x = -1 
      constructor
      · -- Show that -1 is in the interval
        norm_num
      · -- Verify the equation
        have h1 : Real.sqrt (-1 + 2 : ℝ) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h2 : Real.sqrt (22 - 3 * (-1 : ℝ) : ℝ) = 5 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h1, h2, Real.sq_sqrt (show (-1 + 2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (22 - 3 * (-1 : ℝ) : ℝ) ≥ 0 by norm_num)]
    · -- Case x = 2 
      constructor
      · -- Show that 2 is in the interval
        norm_num
      · -- Verify the equation
        have h3 : Real.sqrt (2 + 2 : ℝ) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h4 : Real.sqrt (22 - 3 * (2 : ℝ) : ℝ) = 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h3, h4, Real.sq_sqrt (show (2 + 2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (22 - 3 * (2 : ℝ) : ℝ) ≥ 0 by norm_num)]