import Mathlib

theorem algebra_219174 :
    {x : ℝ | 1 ≤ x ∧ x^2 - 8 * (x + 3) * Real.sqrt (x - 1) + 22 * x - 7 = 0} = {5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the set {x : ℝ | 1 ≤ x ∧ x^2 - 8 * (x + 3) * Real.sqrt (x - 1) + 22 * x - 7 = 0}
    intro h
    rcases h with ⟨hx1, heq⟩
    have h2 : Real.sqrt (x - 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : Real.sqrt (x - 1) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have eq1 : (Real.sqrt (x - 1) - 2) ^ 4 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (x - 1) - 2), sq_nonneg (Real.sqrt (x - 1) ^ 2 - (x - 1)), 
        sq_nonneg (x - 5), Real.sqrt_nonneg (x - 1),
        mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (x - 1)), 
        sq_nonneg (Real.sqrt (x - 1) - 2)]
    have eq2 : Real.sqrt (x - 1) - 2 = 0 := by
      have h4 : (Real.sqrt (x - 1) - 2) ^ 4 = 0 := eq1
      have : Real.sqrt (x - 1) - 2 = 0 := by
        have h1 : (Real.sqrt (x - 1) - 2) ^ 4 = 0 := h4
        simp at h1 ⊢
        <;> nlinarith
      assumption
    have eq3 : Real.sqrt (x - 1) = 2 := by linarith
    have eq4 : x - 1 = 4 := by
      calc
        x - 1 = Real.sqrt (x - 1) ^ 2 := by 
          rw [Real.sq_sqrt]
          linarith
        _ = 2 ^ 2 := by
          rw [eq3]
        _ = (4 : ℝ) := by norm_num
    have hx2 : x = 5 := by linarith
    linarith
  · -- Assume x = 5
    intro hx
    rw [hx]
    constructor
    · norm_num
    · -- Show the equation
      have h1 : Real.sqrt ((5 : ℝ) - 1) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h1, Real.sqrt_nonneg ((5 : ℝ) - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) - 1 by norm_num)]