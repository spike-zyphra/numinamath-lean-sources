import Mathlib

theorem algebra_11929 :
  {x | x > 0 ∧ 12 - x ≥ 0 ∧ 12 * x - x ^ 3 ≥ 0 ∧ x * Real.sqrt (12 - x) + Real.sqrt (12 * x - x ^ 3) ≥ 12} = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if x in the left set, then x = 3
    rintro ⟨hx1, h1, h2, h3⟩
    have h3' : Real.sqrt (12 - x) ≥ 0 := by positivity
    have h4' : Real.sqrt (12 * x - x ^ 3) ≥ 0 := by positivity
    have h6' : (x * Real.sqrt (12 - x) + Real.sqrt (12 * x - x ^ 3)) ^ 2 = 144 := by
      nlinarith [sq_nonneg (x * Real.sqrt (12 - x) + Real.sqrt (12 * x - x ^ 3) - 12), 
        sq_nonneg (Real.sqrt (12 * x - x ^ 3) - 3), 
        sq_nonneg (Real.sqrt (12 - x) - 3), 
        h3, Real.sqrt_nonneg (12 - x), Real.sqrt_nonneg (12 * x - x ^ 3), 
        Real.sq_sqrt (show 0 ≤ (12 - x : ℝ) by linarith), 
        Real.sq_sqrt (show 0 ≤ (12 * x - x ^ 3 : ℝ) by nlinarith), 
        mul_nonneg (Real.sqrt_nonneg (12 - x)) (Real.sqrt_nonneg (12 * x - x ^ 3)), 
        sq_nonneg (x - 3), 
        h1, h2]
    have eq2 : (x * Real.sqrt (12 - x) + Real.sqrt (12 * x - x ^ 3)) ^ 2 =
        x^2 * (12 - x) + (12 * x - x ^ 3) + 2 * x * Real.sqrt (12 - x) * Real.sqrt (12 * x - x ^ 3) := by
      nlinarith [Real.sqrt_nonneg (12 - x), Real.sqrt_nonneg (12 * x - x ^ 3), Real.sq_sqrt (show 0 ≤ (12 - x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (12 * x - x ^ 3 : ℝ) by nlinarith), mul_nonneg (Real.sqrt_nonneg (12 - x)) (Real.sqrt_nonneg (12 * x - x ^ 3))]
    rw [eq2] at h6'
    have h18 : (x - 3) ^ 2 = 0 := by
      nlinarith [Real.sqrt_nonneg (12 - x), Real.sqrt_nonneg (12 * x - x ^ 3), Real.sq_sqrt (show 0 ≤ (12 - x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (12 * x - x ^ 3 : ℝ) by nlinarith), 
        mul_nonneg (Real.sqrt_nonneg (12 - x)) (Real.sqrt_nonneg (12 * x - x ^ 3)), sq_nonneg (x - 3), 
        sq_nonneg (Real.sqrt (12 * x - x ^ 3) - 3), sq_nonneg (Real.sqrt (12 - x) - 3)
      ]
    have h20 : x - 3 = 0 := by
      nlinarith 
    linarith
  · -- Show 3 is in the left side
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · nlinarith [Real.sqrt_nonneg (12 - (3 : ℝ)), Real.sqrt_nonneg (12 * 3 - (3 : ℝ) ^ 3), Real.sq_sqrt (show 0 ≤ (12 - (3 : ℝ) : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (12 * (3 : ℝ) - (3 : ℝ) ^ 3 : ℝ) by norm_num)]
    · -- Show the inequality
      have h1 : Real.sqrt (12 - (3 : ℝ)) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (12 * (3 : ℝ) - (3 : ℝ) ^ 3) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num