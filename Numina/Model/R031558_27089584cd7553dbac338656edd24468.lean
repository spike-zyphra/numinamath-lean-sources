import Mathlib

open Real
open scoped BigOperators

theorem algebra_3074 (a b c : ℤ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a > b) (h₂ : a > c) (h₃ : b > c) (h₄ : a^2 + 2 * b - 10 * c - 16 = 0)
  (h₅ : a + 2 * b - 5 * c - 1 = 0) :
  (1 / 2) * a * b * sin (arccos ((a^2 + b^2 - c^2) / (2 * a * b))) = 2 * sqrt 14 := by
  have h6 : a = 6 := by
    nlinarith [sq_nonneg (a - 6), sq_nonneg (b - 5), sq_nonneg (c - 3),
      h₀.1, h₀.2.1, h₀.2.2, h₁, h₂, h₃]
  have h7 : b = 5 := by
    nlinarith [sq_nonneg (a - 6), sq_nonneg (b - 5), sq_nonneg (c - 3),
      h₀.1, h₀.2.1, h₀.2.2, h₁, h₂, h₃]
  have h8 : c = 3 := by
    nlinarith [sq_nonneg (a - 6), sq_nonneg (b - 5), sq_nonneg (c - 3),
      h₀.1, h₀.2.1, h₀.2.2, h₁, h₂, h₃]
  have h9 : (a : ℝ) = 6 := by exact_mod_cast h6
  have h10 : (b : ℝ) = 5 := by exact_mod_cast h7
  have h11 : (c : ℝ) = 3 := by exact_mod_cast h8
  have h12 : (a^2 + b^2 - c^2 : ℝ) / (2 * a * b) = (13 / 15 : ℝ) := by
    rw [h9, h10, h11]
    norm_num
  have h13 : sin (arccos ((a^2 + b^2 - c^2) / (2 * a * b))) = (2 * Real.sqrt 14 / 15 : ℝ) := by
    rw [h12]
    have h1 : sin (arccos (13 / 15 : ℝ)) = Real.sqrt (1 - (13 / 15 : ℝ) ^ 2) := by
      rw [sin_arccos]
      all_goals norm_num
    rw [h1]
    have h2 : Real.sqrt (1 - (13 / 15 : ℝ) ^ 2) = (Real.sqrt 14 / 15 * 2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h2]
    <;> ring_nf <;> norm_num
  rw [h13]
  rw [h9, h10]
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num