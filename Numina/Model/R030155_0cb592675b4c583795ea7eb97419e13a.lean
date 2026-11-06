import Mathlib

theorem algebra_252495 :
    {x : ℝ | 0 ≤ x + 5 ∧ 0 ≤ 2 * x + 8 ∧ Real.sqrt (x + 5) + Real.sqrt (2 * x + 8) = 7} = {4} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if in the set, then x = 4
    intro h
    rcases h with ⟨hx1, hx2, heq⟩
    have h1 : Real.sqrt (x + 5) ≥ 0 := by positivity
    have h2 : Real.sqrt (2 * x + 8) ≥ 0 := by positivity
    have eq1 : (Real.sqrt (x + 5) + Real.sqrt (2 * x + 8)) ^ 2 = (7 : ℝ) ^ 2 := by 
      rw [heq]
    have eq2 : (Real.sqrt (x + 5) + Real.sqrt (2 * x + 8)) ^ 2 = (Real.sqrt (x + 5)) ^ 2 + (Real.sqrt (2 * x + 8)) ^ 2 + 2 * (Real.sqrt (x + 5) * Real.sqrt (2 * x + 8)) := by 
      ring
    have eq3 : (Real.sqrt (x + 5)) ^ 2 = x + 5 := by 
      rw [Real.sq_sqrt]
      linarith
    have eq4 : (Real.sqrt (2 * x + 8)) ^ 2 = 2 * x + 8 := by 
      rw [Real.sq_sqrt]
      linarith
    -- Now substitute these into eq1
    rw [eq2, eq3, eq4] at eq1
    -- From algebra, we know this leads to a quadratic equation x² - 288x + 1136 = 0
    -- Solving yields x = 4 or x = 284. Only x = 4 is valid.
    have h3 : (x - 4) * (x - 284) = 0 := by 
      nlinarith [Real.sqrt_nonneg (x + 5), Real.sqrt_nonneg (2 * x + 8), 
          sq_nonneg (Real.sqrt (x + 5) - Real.sqrt (2 * x + 8)), 
          sq_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x + 5 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (2 * x + 8 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg (x + 5)) (Real.sqrt_nonneg (2 * x + 8))
        ]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- First case, when x - 4 =0
      linarith
    · -- Second case, when x - 284=0
      nlinarith [Real.sqrt_nonneg (x + 5), Real.sqrt_nonneg (2 * x + 8), 
          Real.sq_sqrt (show 0 ≤ (x + 5 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (2 * x + 8 : ℝ) by linarith)
        ]
  · -- Second direction: if x =4 then in the set
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show sqrt(9) + sqrt(16) = 7.
      have h1 : Real.sqrt (4 + 5) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (2 * (4 : ℝ) + 8) = 4 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num