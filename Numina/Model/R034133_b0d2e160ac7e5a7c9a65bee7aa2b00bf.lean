import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319826 (f : ℝ → ℝ) (hf : f = λ x => 113 * sqrt (x ^ 2 + 3) - 110 * x) :
    IsLeast (range f) (3 * sqrt 223) := by
  constructor
  · -- Show 3 * sqrt 223 is achieved at x = 110 / sqrt 223
    use (110 / Real.sqrt 223)
    rw [hf]
    have h1 : Real.sqrt ((110 / Real.sqrt 223) ^ 2 + 3) = 113 / Real.sqrt 223 := by
      have h2 : ((110 / Real.sqrt 223) ^ 2 + 3) = (113 ^ 2) / (223 : ℝ) := by
        have hsqrt223 : (Real.sqrt 223 : ℝ) ^ 2 = 223 := Real.sq_sqrt (show 0 ≤ (223 : ℝ) by norm_num)
        field_simp
        <;> nlinarith
      rw [h2]
      have hsqrt : Real.sqrt ((113 ^ 2 : ℝ) / (223 : ℝ)) = (113 : ℝ) / Real.sqrt (223 : ℝ) := by
        rw [Real.sqrt_div (by norm_num)]
        have h113 : Real.sqrt ((113 : ℝ) ^ 2) = (113 : ℝ) := Real.sqrt_sq (by linarith)
        rw [h113]
      rw [hsqrt]
      all_goals norm_num
    simp [h1]
    have hs : (Real.sqrt 223 : ℝ) ^ 2 = (223 : ℝ) := by exact Real.sq_sqrt (show (0 : ℝ) ≤ 223 by norm_num)
    field_simp [hs]
    <;> ring_nf <;> norm_num [Real.sq_sqrt, pow_two]
    <;> ring_nf <;> norm_num [Real.sq_sqrt, pow_two]
  · -- Show it's a lower bound
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h2 : (113 * Real.sqrt (x ^ 2 + 3) - 110 * x) >= (3 * Real.sqrt (223 : ℝ)) := by
      nlinarith [sq_nonneg (113 * Real.sqrt (x ^ 2 + 3) - 110 * Real.sqrt (223) * Real.sqrt (x ^ 2 + 3)), sq_nonneg (x - 110 / Real.sqrt (223)), sq_nonneg (x * Real.sqrt 223 - 110 * Real.sqrt (x^2 + 3) ), sq_nonneg (x * Real.sqrt (x^2 + 3) -110 / Real.sqrt (223) * Real.sqrt (x^2 + 3) ), sq_nonneg (113 * x - 110 * Real.sqrt (x^2 + 3) ), sq_nonneg (Real.sqrt (x^2+3) - 113 / Real.sqrt (223) ), sq_nonneg (x * Real.sqrt (223) - 110), sq_nonneg (Real.sqrt (x^2 + 3) * Real.sqrt (223) - 113 ), Real.sqrt_nonneg (x^2 + 3), Real.sqrt_nonneg (223), mul_nonneg (Real.sqrt_nonneg (x^2 + 3)) (Real.sqrt_nonneg (223)), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 3 : ℝ) by nlinarith), Real.sq_sqrt (show (0:ℝ) ≤ (223 : ℝ) by norm_num), Real.sqrt_nonneg 223, Real.sqrt_nonneg (x ^ 2 + 3)]
    linarith [h2, hx]