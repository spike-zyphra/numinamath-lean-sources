import Mathlib

theorem algebra_296788 :
    {x : ℝ | 0 ≤ x ∧ x + Real.sqrt x + Real.sqrt (x + 2) + Real.sqrt (x ^ 2 + 2 * x) = 3} = {1 / 4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume 0 ≤ x ∧ x + Real.sqrt x + Real.sqrt (x + 2) + Real.sqrt (x ^ 2 + 2 * x) = 3. Then x = 1 / 4.
    rintro ⟨hx1, heq⟩
    have h0 : 0 ≤ x := hx1
    have hx2 : Real.sqrt (x ^ 2 + 2 * x) = Real.sqrt x * Real.sqrt (x + 2) := by
      have h1 : x ^ 2 + 2 * x = x * (x + 2) := by
        nlinarith
      rw [h1]
      have h2 : Real.sqrt (x * (x + 2)) = Real.sqrt x * Real.sqrt (x + 2) := by
        rw [Real.sqrt_mul (by linarith)]
      exact h2
    -- Rewrite the equation with the substitution
    have heq2 : x + Real.sqrt x + Real.sqrt (x + 2) + (Real.sqrt x * Real.sqrt (x + 2)) = 3 := by
      linarith [heq, hx2]
    -- Establish the relation between the square roots
    have h3 : Real.sqrt (x + 2) ^ 2 - Real.sqrt x ^ 2 = 2 := by
      have h3 : Real.sqrt (x + 2) ^ 2 = x + 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h4 : Real.sqrt x ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    -- Now, solve the system using substitution and verification
    have h4 : Real.sqrt (x + 2) ^ 2 = Real.sqrt x ^ 2 + 2 := by linarith
    have hx3 : x = 1 / 4 := by
      nlinarith [sq_nonneg (x - 1 / 4), sq_nonneg (Real.sqrt x - 1 / 2), sq_nonneg (Real.sqrt (x + 2) - 3 / 2), 
          Real.sqrt_nonneg (x), Real.sqrt_nonneg (x + 2), 
          Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (x + 2 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x + 2))
         ]
    linarith
  · -- Show that 1/4 is a solution 
    intro heq 
    rw [heq] 
    constructor 
    · -- Show 0 ≤ (1/4 : ℝ) 
      norm_num 
    · -- Show 1/4 is a solution 
      have h1 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h2 : Real.sqrt ((1 / 4 : ℝ) + 2) = 3 / 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h3 : Real.sqrt ((1 / 4 : ℝ) ^ 2 + 2 * (1 / 4)) = 3 / 4 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h1, h2, h3] 
      norm_num