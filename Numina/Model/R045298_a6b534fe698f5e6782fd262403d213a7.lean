import Mathlib

theorem algebra_324650 :
    Set.ncard {x : ℝ | (x^2 + 4 * x - 2)^2 = (5 * x^2 - 1)^2} = 3 := by
  have h1 : {x : ℝ | (x^2 + 4 * x - 2)^2 = (5 * x^2 - 1)^2} = {1/2, (-2 + Real.sqrt 22)/6, (-2 - Real.sqrt 22)/6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume (x^2 + 4 * x - 2)^2 = (5 * x^2 - 1)^2, prove x ∈ {1/2, ..., ...}
      intro h
      have h2 : (x^2 + 4 * x - 2)^2 - (5 * x^2 - 1)^2 = 0 := by linarith
      have h3 : ((x^2 + 4 * x - 2) - (5 * x^2 - 1)) * ((x^2 + 4 * x - 2) + (5 * x^2 - 1)) = 0 := by
        nlinarith
      have h4 : ((x^2 + 4 * x - 2) - (5 * x^2 - 1)) = -4 * x^2 + 4 * x - 1 := by 
        nlinarith
      have h5 : ((x^2 + 4 * x - 2) + (5 * x^2 - 1)) = 6 * x^2 + 4 * x - 3 := by 
        nlinarith
      rw [h4, h5] at h3
      cases' (mul_eq_zero.1 h3) with h6 h7
      · -- Case $-4x^2+4x-1=0$
        have h8 : -4 * x^2 + 4 * x - 1 = 0 := by
          linarith
        have h9 : (2 * x - 1)^2 = 0 := by
          nlinarith
        have h10 : 2 * x - 1 = 0 := by 
          apply pow_eq_zero 
          exact h9
        left
        linarith
      · -- Case $6x^2+4x-3=0$
        have h10 : 6 * x^2 + 4 * x - 3 = 0 := by 
          linarith
        have h11 : (x - (-2 + Real.sqrt 22)/6) * (x - (-2 - Real.sqrt 22)/6) = 0 := by
          nlinarith [ Real.sqrt_pos.mpr (by norm_num : (22 : ℝ) > 0 ), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num) ]
        cases' (mul_eq_zero.1 h11) with h12 h13
        · -- Case x - (-2 + sqrt(22))/6 = 0
          right 
          left 
          linarith
        · -- Case x - (-2 - sqrt(22))/6 = 0
          right 
          right
          linarith
    · -- Assume x ∈ {1/2, or the other two roots}, prove equality
      rintro (h | h | h)
      · -- Case x = 1/2 
        rw [h]
        norm_num
      · -- Case x = (-2 + Real.sqrt 22)/6 
        rw [h]
        nlinarith [ Real.sqrt_pos.mpr (show (22 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num) ]
      · -- Case x = (-2 - Real.sqrt 22)/6 
        rw [h]
        nlinarith [ Real.sqrt_pos.mpr (show (22 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num) ]
  rw [h1]
  have h2 : (1/2 : ℝ) ≠ (-2 + Real.sqrt 22)/6 := by 
    by_contra h
    nlinarith [ Real.sqrt_pos.mpr (show (22 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num) ]
  have h3 : (1/2 : ℝ) ≠ (-2 - Real.sqrt 22)/6 := by 
    by_contra h
    nlinarith [ Real.sqrt_pos.mpr (show (22 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num) ]
  have h4 : (-2 + Real.sqrt 22)/6 ≠ (-2 - Real.sqrt 22)/6 := by 
    by_contra h 
    nlinarith [ Real.sqrt_pos.mpr (show (22 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num) ]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals 
    try { 
      norm_num [h2, h3, h4] 
    }