import Mathlib

open Real

theorem inequalities_10451 :
    IsLeast {a | ∀ x y : ℝ, 0 < x → 0 < y → 5 * x + 12 * sqrt (x * y) ≤ a * (x + y)} 9 := by
  constructor
  · -- First, we verify that 9 belongs to the set, i.e., the inequality holds for a = 9.
    intro x y hx hy
    have h1 : 0 < x * y := by nlinarith
    have h2 : sqrt (x * y) = sqrt x * sqrt y := by
      rw [Real.sqrt_mul (by positivity)]
    have h3 : 5 * x + 12 * sqrt (x * y) ≤ 9 * (x + y) := by
      rw [h2]
      nlinarith [sq_nonneg (sqrt x - 3 / 2 * sqrt y), sq_nonneg (2 * sqrt x - 3 * sqrt y),
        Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by nlinarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ (y : ℝ) by nlinarith),
        mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
      ]
    linarith
  · -- Now we show that 9 is the least value, so if a is in the set then a ≥ 9.
    intro a ha
    have h4 := ha (9 / 4) 1 (by norm_num) (by norm_num)
    have h2 : sqrt ((9 / 4 : ℝ) * (1 : ℝ)) = 3 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h2] at h4
    norm_num at h4
    linarith