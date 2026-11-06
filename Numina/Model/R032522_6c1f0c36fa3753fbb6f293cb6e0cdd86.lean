import Mathlib

theorem algebra_167146 :
    {x : ℝ | (x - 1991) / 10 ≥ 0 ∧ (x - 1990) / 11 ≥ 0 ∧ (x - 10) / 1991 ≥ 0 ∧
      (x - 11) / 1990 ≥ 0 ∧
      Real.sqrt ((x - 1991) / 10) + Real.sqrt ((x - 1990) / 11) =
      Real.sqrt ((x - 10) / 1991) + Real.sqrt ((x - 11) / 1990)} = 
    {2001} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is a solution, show x = 2001
    rintro ⟨h1, h2, h3, h4, heq⟩
    have h10 : Real.sqrt ((x - 1991) / 10) ≥ 0 := by positivity
    have h11 : Real.sqrt ((x - 1990) / 11) ≥ 0 := by positivity
    have h12 : Real.sqrt ((x - 10) / 1991) ≥ 0 := by positivity
    have h13 : Real.sqrt ((x - 11) / 1990) ≥ 0 := by positivity
    have h_eq1 : Real.sqrt ((x - 1991) / 10) = Real.sqrt ((x - 10) / 1991) := by
      nlinarith [Real.sqrt_nonneg ((x - 1991) / 10), Real.sqrt_nonneg ((x - 1990) / 11), Real.sqrt_nonneg ((x - 10) / 1991), Real.sqrt_nonneg ((x - 11) / 1990), 
        sq_nonneg (Real.sqrt ((x - 1991) / 10) - Real.sqrt ((x - 10) / 1991)), 
        sq_nonneg (Real.sqrt ((x - 1990) / 11) - Real.sqrt ((x - 11) / 1990)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1991) / 10 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1990) / 11 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 10) / 1991 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 11) / 1990 by linarith)
      ]
    have h_eq2 : (x - 1991) / 10 = (x - 10) / 1991 := by
      have h13 : Real.sqrt ((x - 1991) / 10) = Real.sqrt ((x - 10) / 1991) := h_eq1
      have h14 : (Real.sqrt ((x - 1991) / 10)) ^ 2 = (Real.sqrt ((x - 10) / 1991)) ^ 2 := by 
        rw [h13]
      rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] at h14
      linarith
    have h_eq3 : Real.sqrt ((x - 1990) / 11) = Real.sqrt ((x - 11) / 1990) := by
      nlinarith [Real.sqrt_nonneg ((x - 1991) / 10), Real.sqrt_nonneg ((x - 1990) / 11), Real.sqrt_nonneg ((x - 10) / 1991), Real.sqrt_nonneg ((x - 11) / 1990), 
        sq_nonneg (Real.sqrt ((x - 1991) / 10) - Real.sqrt ((x - 10) / 1991)), 
        sq_nonneg (Real.sqrt ((x - 1990) / 11) - Real.sqrt ((x - 11) / 1990)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1991) / 10 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1990) / 11 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 10) / 1991 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 11) / 1990 by linarith)
      ]
    have h_eq4 : (x - 1990) / 11 = (x - 11) / 1990 := by
      have h13 : Real.sqrt ((x - 1990) / 11) = Real.sqrt ((x - 11) / 1990) := h_eq3
      have h14 : (Real.sqrt ((x - 1990) / 11)) ^ 2 = (Real.sqrt ((x - 11) / 1990)) ^ 2 := by 
        rw [h13]
      rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] at h14
      linarith
    nlinarith
  · -- Assume x = 2001, show x is a solution
    intro heq
    rw [heq]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show the equation holds
      have h1 : Real.sqrt ((2001 - 1991) / 10) = 1 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h2 : Real.sqrt ((2001 - 1990) / 11) = 1 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h3 : Real.sqrt ((2001 - 10) / 1991) = 1 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h4 : Real.sqrt ((2001 - 11) / 1990) = 1 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      linarith