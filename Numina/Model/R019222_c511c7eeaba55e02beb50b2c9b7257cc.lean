import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_294869 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c + c * a = 1 ∧ x = sqrt (a * b + 5) + sqrt (b * c + 5) + sqrt (c * a + 5)} (4 * sqrt 3) := by
  constructor
  · -- First, we show that $4\sqrt{3}$ belongs to the set
    use 1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3
    constructor
    · -- Show that 1 / sqrt(3) > 0
      positivity
    constructor
    · -- Show that 1 / sqrt(3) > 0
      positivity
    constructor
    · -- Show that 1 / sqrt(3) > 0
      positivity
    constructor
    · -- Show that (1 / sqrt(3)) * (1 / sqrt(3)) + (1 / sqrt(3)) * (1 / sqrt(3)) + (1 / sqrt(3)) * (1 / sqrt(3)) = 1
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 3]
    · -- Show that 4 * sqrt(3) = sqrt ((1 / sqrt 3) * (1 / sqrt 3) + 5) + sqrt ((1 / sqrt 3) * (1 / sqrt 3) + 5) + sqrt ((1 / sqrt 3) * (1 / sqrt 3) + 5)
      have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h3 : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = 1 / 3 := by
        field_simp [h2]
        <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 3]
      have h4 : sqrt ((1 / Real.sqrt 3) * (1 / Real.sqrt 3) + 5) = 4 * sqrt 3 / 3 := by
        rw [h3]
        have h5 : sqrt (1 / 3 + 5) = sqrt (16 / 3) := by norm_num
        rw [h5]
        have h6 : sqrt (16 / 3) = 4 * sqrt 3 / 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
        rw [h6]
        <;> ring_nf <;> norm_num
      rw [h4]
      ring_nf <;> norm_num
  · -- Now, we need to prove that $4\sqrt{3}$ is the greatest
    rintro x ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : (sqrt (a * b + 5) + sqrt (b * c + 5) + sqrt (c * a + 5)) ^ 2 ≤ 48 := by
      nlinarith [sq_nonneg (sqrt (a * b + 5) - sqrt (b * c + 5)), sq_nonneg (sqrt (b * c + 5) - sqrt (c * a + 5)), sq_nonneg (sqrt (c * a + 5) - sqrt (a * b + 5)),
        Real.sqrt_nonneg (a * b + 5), Real.sqrt_nonneg (b * c + 5), Real.sqrt_nonneg (c * a + 5),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        Real.sq_sqrt (show (0 : ℝ) ≤ a * b + 5 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ b * c + 5 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ c * a + 5 by nlinarith),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h3 : (sqrt (a * b + 5) + sqrt (b * c + 5) + sqrt (c * a + 5)) ≤ 4 * sqrt 3 := by
      nlinarith [h2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt (a * b + 5) + sqrt (b * c + 5) + sqrt (c * a + 5) - 4 * sqrt 3)]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h3, hx]