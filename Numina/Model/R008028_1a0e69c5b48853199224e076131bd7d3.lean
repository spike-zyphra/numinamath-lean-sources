import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_274875 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b + b * c + c * a = 1 ∧ x = a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2)} (4 / 9 * sqrt 3) := by
  constructor
  · -- Let's first show 4/9*√3 is achieved
    use Real.sqrt (1 / 3), Real.sqrt (1 / 3), Real.sqrt (1 / 3)
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · -- Show that sqrt(1/3) ≠ 1
      by_contra h
      have h1 : Real.sqrt (1 / 3) = 1 := by linarith
      have h2 : Real.sqrt (1 / 3) ^ 2 = 1 ^ 2 := by rw [h1]
      norm_num [Real.sq_sqrt] at h2
    constructor
    · -- Show that sqrt(1/3) ≠ 1
      by_contra h
      have h1 : Real.sqrt (1 / 3) = 1 := by linarith
      have h2 : Real.sqrt (1 / 3) ^ 2 = 1 ^ 2 := by rw [h1]
      norm_num [Real.sq_sqrt] at h2
    constructor
    · -- Show that sqrt(1/3) ≠ 1
      by_contra h
      have h1 : Real.sqrt (1 / 3) = 1 := by linarith
      have h2 : Real.sqrt (1 / 3) ^ 2 = 1 ^ 2 := by rw [h1]
      norm_num [Real.sq_sqrt] at h2
    constructor
    · -- Show that a * b + b * c + c * a = 1
      have h3 : Real.sqrt (1 / 3) * Real.sqrt (1 / 3) = 1 / 3 := by
        calc
          Real.sqrt (1 / 3) * Real.sqrt (1 / 3) = (Real.sqrt (1 / 3)) ^ 2 := by ring
          _ = 1 / 3 := by
            rw [Real.sq_sqrt]
            all_goals norm_num
      nlinarith [h3]
    · -- Show that the value of the function is 4/9 * sqrt(3)
      have h4 : Real.sqrt (1 / 3) * (1 - Real.sqrt (1 / 3) ^ 2) * (1 - Real.sqrt (1 / 3) ^ 2) + Real.sqrt (1 / 3) * (1 - Real.sqrt (1 / 3) ^ 2) * (1 - Real.sqrt (1 / 3) ^ 2) + Real.sqrt (1 / 3) * (1 - Real.sqrt (1 / 3) ^ 2) * (1 - Real.sqrt (1 / 3) ^ 2) = 4 / 9 * Real.sqrt 3 := by
        have h5 : Real.sqrt (1 / 3) ^ 2 = 1 / 3 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        have h6 : (1 - Real.sqrt (1 / 3) ^ 2) = 2 / 3 := by
          rw [h5]
          norm_num
        rw [h6]
        have h7 : Real.sqrt (1 / 3) = Real.sqrt 3 / 3 := by
          rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h7]
        ring_nf
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
      linarith [h4]
  · -- Now prove 4/9*sqrt 3 is the greatest value
    intro w
    rintro ⟨a, b, c, ha, hb, hc, ha1, hb1, hc1, h, hw⟩
    have h4 : a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) = 4 * (a * b * c) := by
      nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (b * c - b * a), sq_nonneg (c * a - c * b),
        h, sq_nonneg (a * b + b * c + c * a - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    rw [h4] at hw
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a^2 - 1 / 3), sq_nonneg (b^2 - 1 / 3), sq_nonneg (c^2 - 1 / 3),
      Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0),
      sq_nonneg (sqrt 3 - 1), sq_nonneg (a * b * c),
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0),
      h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]