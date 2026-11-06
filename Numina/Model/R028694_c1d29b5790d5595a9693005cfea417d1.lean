import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_151370 {f : ℝ → ℝ} (hf : f = λ x => 2 - 2 * (cos x)^2 - sin x) :
    IsLeast (range f) (-1 / 8) ∧ IsGreatest (range f) 3 := by
  have h1 : ∀ x : ℝ, f x = 2 * (sin x) ^ 2 - sin x := by
    intro x
    rw [hf]
    have h2 : cos x ^ 2 = 1 - sin x ^ 2 := by
      rw [Real.cos_sq']
    simp [h2]
    <;> ring
  constructor
  · -- Prove that -1/8 is the least element in the range of f
    constructor
    · -- Show that -1/8 is in the range of f
      use Real.arcsin (1 / 4)
      have h2 : sin (Real.arcsin (1 / 4)) = 1 / 4 := by
        apply sin_arcsin
        norm_num
        norm_num
      rw [h1]
      rw [h2]
      norm_num
      all_goals norm_num
    · -- Show that -1/8 is the smallest value
      intro y
      rintro ⟨x, hx⟩
      rw [h1] at hx
      have h2 : -1 ≤ sin x ∧ sin x ≤ 1 := by
        constructor
        · linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
        · linarith [Real.sin_le_one x]
      nlinarith [sq_nonneg (sin x - 1 / 4), sq_nonneg (sin x - 1 / 4), Real.sin_le_one x, Real.neg_one_le_sin x]
  · -- Prove that 3 is the greatest element in the range of f
    constructor
    · -- Show that 3 is in the range of f
      use (3 * Real.pi / 2)
      have h2 : sin (3 * Real.pi / 2) = -1 := by
        have h2 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
        rw [h2]
        have h3 : sin (Real.pi + Real.pi / 2) = -1 := by
          rw [sin_add, sin_pi, cos_pi]
          norm_num [sin_pi_div_two, cos_pi_div_two]
          <;> ring
        exact h3
      rw [h1]
      rw [h2]
      all_goals norm_num
    · -- Show that 3 is the greatest value
      intro y
      rintro ⟨x, hx⟩
      rw [h1] at hx
      have h2 : -1 ≤ sin x ∧ sin x ≤ 1 := by
        constructor
        · linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
        · linarith [Real.sin_le_one x]
      nlinarith [sq_nonneg (sin x + 1), sq_nonneg (sin x - 1 / 4), Real.sin_le_one x, Real.neg_one_le_sin x]