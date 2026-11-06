import Mathlib

theorem algebra_15612 :
  {x : ℝ | x > 0 ∧ √(8*x) * √(10*x) * √(3*x) * √(15*x) = 15} = {1 / 2} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the set, prove x = 1/2
    rintro ⟨hx, h⟩
    have h1 : √(8 * x) * √(10 * x) * √(3 * x) * √(15 * x) = √((8 * x) * (10 * x) * (3 * x) * (15 * x)) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [h1] at h
    have h2 : (8 * x) * (10 * x) * (3 * x) * (15 * x) = 225 := by
      have h3 : √((8 * x) * (10 * x) * (3 * x) * (15 * x)) = 15 := h
      have h4 : (√((8 * x) * (10 * x) * (3 * x) * (15 * x))) ^ 2 = (15:ℝ) ^ 2 := by 
        rw [h3]
      rw [Real.sq_sqrt (by positivity)] at h4
      nlinarith
    have h3 : (8 * x) * (10 * x) * (3 * x) * (15 * x) = 3600 * (x ^ 4) := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x)]
    rw [h3] at h2
    have h4 : x ^ 4 = (1 / 16) := by
      nlinarith
    have h5 : x ^ 2 = (1 / 4) := by
      nlinarith [sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2)]
    have h6 : x = 1 / 2 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]
    linarith 
  · -- Assume x = 1/2, prove in the set.
    intro h 
    rw [h] 
    constructor
    · norm_num 
    · -- Verify the product 
      have h1 : √(8 * (1 / 2 : ℝ)) * √(10 * (1 / 2 : ℝ)) * √(3 * (1 / 2 : ℝ)) * √(15 * (1 / 2 : ℝ)) =
          √((8 * (1 / 2 : ℝ)) * (10 * (1 / 2 : ℝ)) * (3 * (1 / 2 : ℝ)) * (15 * (1 / 2 : ℝ))) := by 
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      rw [h1]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      <;> nlinarith