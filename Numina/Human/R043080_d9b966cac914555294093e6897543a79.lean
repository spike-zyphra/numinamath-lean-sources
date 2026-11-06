import Mathlib

open Real Set
open scoped BigOperators

/-For $0 \le x \le 40$ and $0 \le y \le 50,$ find the minimum value of
\[\sqrt{x^2 + 400} + \sqrt{y^2 + 900} + \sqrt{x^2 + y^2 - 80x - 100y + 4100}.\]-/
theorem algebra_20858 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x ∈ Icc 0 40 ∧ y ∈ Icc 0 50 ∧
    z = sqrt (x^2 + 400) + sqrt (y^2 + 900) +
      sqrt (x^2 + y^2 - 80 * x - 100 * y + 4100)} (70 * sqrt 2) := by
  constructor
  · -- Prove that 70 * sqrt 2 is in the set
    simp
    use 20
    norm_num
    use 30
    norm_num
    rw [show (800 : ℝ) = 20^2 * 2 by linarith, show (1800 : ℝ) = 30^2 * 2 by linarith]
    rw [Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_sq, Real.sqrt_sq]
    repeat linarith
  · -- Prove that 70 * sqrt 2 is the least element
    apply mem_lowerBounds.mpr
    simp
    intro v x hx₁ hx₂ y hy₁ hy₂ hv
    rw [hv]
    -- QM-AM
    have QM_AM: ∀x, ∀y, √2 * (x + y) / 2 ≤ √(x^2 + y^2) := by
      intro x y
      by_cases h: x + y < 0
      · have : √2 * (x + y) / 2 ≤ 0 := by
          rw [mul_div_right_comm]
          apply mul_nonpos_of_nonneg_of_nonpos
          positivity
          linarith
        apply le_trans this (by positivity)
      rw [Real.le_sqrt]
      ring_nf
      rw [show √2 ^ 2 = 2 by rw [Real.sq_sqrt (by simp)]]
      linarith [two_mul_le_add_sq x y]
      rw [mul_div_right_comm]
      refine (mul_nonneg_iff_right_nonneg_of_pos ?_).mpr ?_
      positivity
      linarith
      positivity
    -- End QM-AM
    have : 70 * √2 = √2 * (x + 20) / 2 +  √2 * (y + 30) / 2 + √2 * (40 - x + (50 - y)) / 2 := by ring_nf
    rw [this]
    apply add_le_add
    rw [show (400 : ℝ) = 20^2 by linarith, show (900 : ℝ) = 30^2 by linarith]
    exact add_le_add (QM_AM x 20) (QM_AM y 30)
    have : (x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) = (40 - x)^2 + (50 - y)^2 := by ring_nf
    rw [this]
    apply QM_AM
