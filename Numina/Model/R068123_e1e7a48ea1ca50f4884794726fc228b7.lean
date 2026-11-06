import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_145513 (f : ℝ → ℝ → ℝ)
  (hf : f = λ x y => x^2 + y^2 - 2 * x - y)
  (φ : ℝ → ℝ → ℝ)
  (φ_def : φ = λ x y => x + y - 1) :
  IsLeast {z | ∃ x y, z = f x y ∧ φ x y = 0} (-1.125) := by
  constructor
  · -- Show that -1.125 is in the set
    use 3 / 4, 1 / 4
    constructor
    · -- Show that -1.125 = f (3/4) (1/4)
      rw [hf]
      norm_num
    · -- Show that φ (3/4) (1/4) = 0
      rw [φ_def]
      norm_num
  · -- Show that if z in the set, then z ≥ -1.125
    intro z h
    rcases h with ⟨x, y, hz, hφ⟩
    rw [hf] at hz
    simp at hz
    rw [φ_def] at hφ
    simp at hφ
    have h_eq : y = 1 - x := by linarith
    rw [h_eq] at hz
    have h : 2 * (x - 3 / 4) ^ 2 ≥ 0 := by
      apply mul_nonneg
      norm_num
      apply pow_two_nonneg
    nlinarith