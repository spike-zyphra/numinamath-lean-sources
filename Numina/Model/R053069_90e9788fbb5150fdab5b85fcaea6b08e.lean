import Mathlib

theorem algebra_22546 :
    IsGreatest {x | ∃ a b : ℝ, x = (a + b)^2 ∧ a^2 + b^2 = 1} 2 := by
  constructor
  · -- Show that 2 is in the set.
    use Real.sqrt (1 / 2), Real.sqrt (1 / 2)
    constructor
    · -- Show that (sqrt(1/2) + sqrt(1/2)) ^ 2 = 2
      have h1 : Real.sqrt (1 / 2 : ℝ) + Real.sqrt (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
        have h2 : Real.sqrt (2 : ℝ) = 2 * Real.sqrt (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf <;> norm_num [Real.sq_sqrt]
        linarith [h2]
      rw [h1]
      rw [Real.sq_sqrt (by norm_num)]
    · -- Show that (sqrt(1/2)) ^ 2 + (sqrt(1/2)) ^ 2 = 1
      have h2 : (Real.sqrt (1 / 2 : ℝ) ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
      nlinarith
  · -- Show that 2 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, h1, h2⟩
    -- We need to show x = (a + b)² ≤ 2 given a² + b² = 1
    nlinarith [sq_nonneg (a - b)]