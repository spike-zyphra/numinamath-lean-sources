import Mathlib

theorem algebra_3091 : IsLeast {x | ∃ a b : ℝ, x = Real.sqrt (a ^ 2 - 2 * a + b ^ 2 - 4 * b + 5) +
    Real.sqrt (a ^ 2 + 28 * a + b ^ 2 + 36 * b + 520)} 25 := by
  constructor
  · -- Show 25 is in the set.
    use -13 / 2, -8
    have h1 : Real.sqrt ((-13 / 2 : ℝ) ^ 2 - 2 * (-13 / 2) + (-8 : ℝ) ^ 2 - 4 * (-8) + 5) = 25 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h2 : Real.sqrt ((-13 / 2 : ℝ) ^ 2 + 28 * (-13 / 2) + (-8 : ℝ) ^ 2 + 36 * (-8) + 520) = 25 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show 25 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, hx⟩
    have h1 : Real.sqrt (a ^ 2 - 2 * a + b ^ 2 - 4 * b + 5) + Real.sqrt (a ^ 2 + 28 * a + b ^ 2 + 36 * b + 520) ≥ 25 := by
      have h2 : Real.sqrt (a ^ 2 - 2 * a + b ^ 2 - 4 * b + 5) = Real.sqrt ((a - 1) ^ 2 + (b - 2) ^ 2) := by
        have h3 : a ^ 2 - 2 * a + b ^ 2 - 4 * b + 5 = (a - 1) ^ 2 + (b - 2) ^ 2 := by
          nlinarith
        rw [h3]
      have h4 : Real.sqrt (a ^ 2 + 28 * a + b ^ 2 + 36 * b + 520) = Real.sqrt ((a + 14) ^ 2 + (b + 18) ^ 2) := by
        have h5 : a ^ 2 + 28 * a + b ^ 2 + 36 * b + 520 = (a + 14) ^ 2 + (b + 18) ^ 2 := by
          nlinarith
        rw [h5]
      rw [h2, h4]
      have h5 : Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) ≥ 0 := by positivity
      have h6 : Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2) ≥ 0 := by positivity
      have h7 : Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) + Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2) ≥ 25 := by
        have h8 : (Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) + Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2)) ^ 2 ≥ 625 := by
          have h10 : Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) ^ 2 = (a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2 := by
            apply Real.sq_sqrt
            positivity
          have h11 : Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2) ^ 2 = (a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2 := by
            apply Real.sq_sqrt
            positivity
          have h9 : (Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) + Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2)) ^ 2 =
              Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) ^ 2 + Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2) ^ 2 + 2 * (Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) * Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2)) := by ring
          nlinarith [sq_nonneg ((a - 1 : ℝ) - (a + 14) * 3 / 5), sq_nonneg ((b - 2 : ℝ) - (b + 18) * 3 / 5),
            Real.sqrt_nonneg ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2),
            Real.sqrt_nonneg ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2),
            mul_nonneg (Real.sqrt_nonneg ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2)) (Real.sqrt_nonneg ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2)),
            Real.sq_sqrt (show ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) ≥ 0 by positivity),
            Real.sq_sqrt (show ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2) ≥ 0 by positivity),
            sq_nonneg ((a - 1 : ℝ) * (b + 18 : ℝ) - (b - 2 : ℝ) * (a + 14 : ℝ)),
            sq_nonneg ((a + 14 : ℝ) * (a + 14 : ℝ) + (b + 18 : ℝ) * (b + 18 : ℝ))
          ]
        have h9 : Real.sqrt ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2) + Real.sqrt ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg ((a - 1 : ℝ) ^ 2 + (b - 2 : ℝ) ^ 2), Real.sqrt_nonneg ((a + 14 : ℝ) ^ 2 + (b + 18 : ℝ) ^ 2)]
      linarith
    linarith [show Real.sqrt (a ^ 2 - 2 * a + b ^ 2 - 4 * b + 5) + Real.sqrt (a ^ 2 + 28 * a + b ^ 2 + 36 * b + 520) ≥ 25 by linarith [h1]]