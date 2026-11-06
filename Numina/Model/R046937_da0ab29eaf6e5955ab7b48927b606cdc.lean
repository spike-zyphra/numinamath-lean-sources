import Mathlib

theorem algebra_14916 :
  {x : ℝ | √((-2 - x) ^ 2 + (0 - 0) ^ 2) = √((0 - x) ^ 2 + (4 - 0) ^ 2)} = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the square roots are equal, prove x = 3
    intro h
    have h1 : (-2 - x) ^ 2 + (0 - 0) ^ 2 = (0 - x) ^ 2 + (4 - 0) ^ 2 := by
      have h2 : √((-2 - x) ^ 2 + (0 - 0) ^ 2) = √((0 - x) ^ 2 + (4 - 0) ^ 2) := h
      have h3 : (-2 - x) ^ 2 + (0 - 0) ^ 2 ≥ 0 := by
        nlinarith
      have h4 : (0 - x) ^ 2 + (4 - 0) ^ 2 ≥ 0 := by
        nlinarith
      have h5 : (-2 - x) ^ 2 + (0 - 0) ^ 2 = (0 - x) ^ 2 + (4 - 0) ^ 2 := by 
        rw [Real.sqrt_inj (by nlinarith) (by nlinarith)] at h2
        linarith
      exact h5 
    have hx : x = 3 := by 
      nlinarith
    exact_mod_cast hx 
  · -- Assume x = 3, prove the square roots are equal
    intro h
    rw [h]
    have h2 : √((-2 - (3 : ℝ)) ^ 2 + (0 - 0 : ℝ) ^ 2) = √((0 - (3 : ℝ)) ^ 2 + (4 - 0 : ℝ) ^ 2) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    exact_mod_cast h2