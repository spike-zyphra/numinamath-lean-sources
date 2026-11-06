import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_181066 :
  IsGreatest {x | ∃ a b c : ℝ, x = a - b ∧ a + b + c = 2 ∧ a * b + b * c + c * a = 1} (2 * sqrt 3 / 3) := by
  constructor
  · -- Show $2 \sqrt{3} / 3$ is achievable
    use (2 + Real.sqrt 3) / 3, (2 - Real.sqrt 3) / 3, 2 / 3
    constructor
    · -- Show $2 \sqrt{3} / 3 = a - b$
      field_simp
      <;> ring_nf <;> norm_num
    constructor
    · -- Show $a + b + c = 2$
      ring_nf
    · -- Show $a \cdot b + b \cdot c + c \cdot a = 1$
      have h1 : (Real.sqrt 3) ^ 2 = 3 := by
        exact Real.sq_sqrt (show 0 ≤ 3 by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), h1]
  · -- Show $2 \sqrt{3} / 3$ is greatest
    rintro x ⟨a, b, c, hx, h1, h2⟩
    rw [hx]
    nlinarith [sq_nonneg (a - b - 2 * Real.sqrt 3 / 3), sq_nonneg (c - 2 / 3), sq_nonneg (a + b - 4 / 3), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a - b + 2 * Real.sqrt 3 / 3)]