import Mathlib

theorem algebra_15378 : {x | x ≥ 0 ∧ √x + 2 * √(x ^ 2 + 7 * x) + √(x + 7) = 35 - 2 * x} = {841/144} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h: x ≥ 0 ∧ √x + 2 * √(x ^ 2 + 7 * x) + √(x + 7) = 35 - 2 * x
    rintro ⟨hx, heq⟩
    
    have h1 : √x ≥ 0 := Real.sqrt_nonneg x
    have h2 : √(x + 7) ≥ 0 := Real.sqrt_nonneg (x + 7)
    have h3 : √(x ^ 2 + 7 * x) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 7 * x)
    
    have h4 : 35 - 2 * x ≥ 0 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 7), Real.sqrt_nonneg (x ^ 2 + 7 * x), heq]
    
    have eq1 : (√x + √(x + 7)) ^ 2 = 2 * x + 7 + 2 * √(x ^ 2 + 7 * x) := by
      have h11 : √x ^ 2 = x := Real.sq_sqrt (by linarith)
      have h12 : √(x + 7) ^ 2 = x + 7 := Real.sq_sqrt (by linarith)
      have h13 : √x * √(x + 7) = √(x ^ 2 + 7 * x) := by 
        have h44 : √x * √(x + 7) = √(x * (x + 7)) := by 
          rw [← Real.sqrt_mul (by nlinarith)]
        have h45 : x * (x + 7) = x ^ 2 + 7 * x := by ring
        rw [h45] at h44
        linarith
      nlinarith [h11, h12, h13]
    
    have h5 : x = (841 / 144 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 7 * x), Real.sq_sqrt (show (x ^ 2 + 7 * x) ≥ 0 by nlinarith), Real.sq_sqrt (show x ≥ 0 by linarith), Real.sq_sqrt (show x + 7 ≥ 0 by nlinarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x + 7)), h4]
    
    linarith
  
  · -- Show that 841/144 satisfies the equation.
    intro heq
    rw [heq] at *
    constructor 
    · -- Show x ≥ 0.
      norm_num
    · -- Show the equation is satisfied.
      have h1 : √(841 / 144 : ℝ) = (29 / 12 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  
      have h2 : √((841 / 144 : ℝ) ^ 2 + 7 * (841 / 144 : ℝ)) = (1247 / 144 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  
      have h3 : √((841 / 144 : ℝ) + 7) = (43 / 12 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  
      rw [h1, h2, h3]
      norm_num