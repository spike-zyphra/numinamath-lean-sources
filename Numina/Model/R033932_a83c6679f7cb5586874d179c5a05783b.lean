import Mathlib

theorem algebra_213824 :
    {(x, y) : ℝ × ℝ | (3 * x - 2 ≥ 0) ∧ (4 * y - 3 ≥ 0) ∧ 
      (x^2 - 4 * Real.sqrt (3 * x - 2) + 10 = 2 * y) ∧
      (y^2 - 6 * Real.sqrt (4 * y - 3) + 11 = x)} =
    {(2, 3)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (x, y) in the LHS set; prove (x,y)=(2,3)
    rintro ⟨h1_nonneg, h2_nonneg, he1, he2⟩
  
    have h3 : 0 ≤ Real.sqrt (3 * x - 2) := Real.sqrt_nonneg (3 * x - 2)
    have h4 : 0 ≤ Real.sqrt (4 * y - 3) := Real.sqrt_nonneg (4 * y - 3)
  
    have h5 : (Real.sqrt (3 * x - 2)) ^ 2 = 3 * x - 2 := Real.sq_sqrt (by linarith)
    have h6 : (Real.sqrt (4 * y - 3)) ^ 2 = 4 * y - 3 := Real.sq_sqrt (by linarith)
    
    have h7 : x = 2 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), 
          sq_nonneg (Real.sqrt (3 * x - 2) - 2), sq_nonneg (Real.sqrt (4 * y - 3) - 3), 
          Real.sqrt_nonneg (3 * x - 2), Real.sqrt_nonneg (4 * y - 3), 
          mul_nonneg (Real.sqrt_nonneg (3 * x - 2)) (Real.sqrt_nonneg (4 * y - 3))]
  
    have h8 : y = 3 := by 
      have h9 : Real.sqrt (3 * x - 2) = 2 := by
        rw [show (3 * x - 2 : ℝ) = 4 by
          nlinarith [h7, h1_nonneg]
        ]
        exact Real.sqrt_eq_cases.mpr (by norm_num)
      have he1_sub : x ^ 2 - 4 * Real.sqrt (3 * x - 2) + 10 = 2 * y := he1
      rw [h9] at he1_sub
      have eq1 := he1_sub
      rw [show (x : ℝ) = (2 : ℝ) by linarith [h7]] at eq1
      nlinarith
  
    simp [h7, h8] 
  · -- Show that (2, 3) is in the set
    rintro ⟨rfl, rfl⟩
    
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that 2^2 - 4 * sqrt(3*2 - 2) + 10 = 2*3
      have h1 : Real.sqrt (3 * (2 : ℝ) - 2) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- Show that 3^2 - 6 * sqrt(4*3 - 3) + 11 = 2
      have h2 : Real.sqrt (4 * (3 : ℝ) - 3) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      norm_num