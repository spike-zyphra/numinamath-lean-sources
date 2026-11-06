import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190035 (f : ℝ → ℝ) (hf : f = λ x => x^2 * 3^x - 3^(x + 1)) :
    ∀ x, f x ≤ 0 ↔ x ∈ Icc (-sqrt 3) (sqrt 3) := by
  intro x
  have hfx : f x = (x ^ 2 - 3) * (3 : ℝ) ^ x := by
    rw [hf]
    have h1 : (3 : ℝ) ^ (x + 1) = (3 : ℝ) ^ x * 3 := by
      rw [Real.rpow_add]
      norm_num
      all_goals linarith
    simp [h1]
    <;> ring_nf <;> simp [Real.rpow_mul] <;> ring_nf <;> norm_num
    <;> ring
  rw [hfx]
  have h1 : (3 : ℝ) ^ x > 0 := by positivity
  constructor
  · -- Forward implication: f(x) ≤ 0 then x ∈ [-√3, √3]
    intro h
    have h2 : x ^ 2 - 3 ≤ 0 := by nlinarith [h1, h]
    have h3 : x ^ 2 ≤ 3 := by linarith
    constructor
    · -- Show that -√3 ≤ x
      have h4 : -Real.sqrt 3 ≤ x := by
        have h5 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
        nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sqrt_nonneg 3]
      linarith
    · -- Show that x ≤ √3
      have h6 : x ≤ Real.sqrt 3 := by
        have h7 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
        nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sqrt_nonneg 3]
      linarith
  · -- Backward implication: x ∈ [-√3, √3] then f(x) ≤ 0
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 ≤ 3 := by
      have h4 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
      have h5 : x ^ 2 ≤ (Real.sqrt 3) ^ 2 := by nlinarith [Real.sqrt_nonneg 3]
      have h6 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
      nlinarith
    have h4 : x ^ 2 - 3 ≤ 0 := by linarith
    nlinarith [h4, Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) x]