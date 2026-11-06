import Mathlib

open Finset Real

theorem algebra_4753 : ∑ i ∈ range 2017, (1 / (√(i + 1) + √(i + 2))) = √2018 - 1 := by
  have h1 : ∀ i : ℕ, 1 / (√(i + 1) + √(i + 2)) = √(i + 2) - √(i + 1) := by
    intro i
    have h2 : √(i + 1) + √(i + 2) ≠ 0 := by
      positivity
    field_simp [(show √(i + 1) + √(i + 2) ≠ 0 by assumption)]
    <;> nlinarith [Real.sqrt_nonneg (i + 1), Real.sqrt_nonneg (i + 2),
        Real.sq_sqrt (show (0 : ℝ) ≤ i + 1 by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ i + 2 by linarith),
        sq_nonneg (√(i + 2) - √(i + 1)), sq_nonneg (√(i + 2) + √(i + 1))
      ]
  rw [sum_congr rfl (fun i hi => h1 i)]
  have h3 : ∀ n : ℕ, ∑ i ∈ range n, (√(i + 2) - √(i + 1)) = √(n + 1) - 1 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp
      <;> ring_nf <;> norm_num
  specialize h3 2017
  norm_num at h3 ⊢
  <;> nlinarith [Real.sqrt_nonneg (2017 : ℝ), Real.sqrt_nonneg (2018 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2017 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2018 : ℝ) by norm_num)]