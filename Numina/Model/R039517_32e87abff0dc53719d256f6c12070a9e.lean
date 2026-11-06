import Mathlib

open Real Set
open scoped Real

theorem algebra_9408 (f : ℝ → ℝ) (hf : f = λ x => 3 - 4 * sin x - cos x ^ 2) :
    IsGreatest (range f) 7 ∧ IsLeast (range f) (-1) := by
  constructor
  · -- Show that 7 is greatest in range of f
    constructor
    · -- Show that 7 is in the range of f
      use (3 * Real.pi / 2)
      rw [hf]
      have h1 : sin (3 * Real.pi / 2) = -1 := by
          have h2 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
          rw [h2]
          rw [sin_add, sin_pi, cos_pi]
          norm_num [sin_pi_div_two, cos_pi_div_two]
      have h2 : cos (3 * Real.pi / 2) = 0 := by
          have h3 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
          rw [h3]
          rw [cos_add, sin_pi, cos_pi]
          norm_num [sin_pi_div_two, cos_pi_div_two]
      simp [h1, h2]
      all_goals linarith
    · -- Show that no greater element is in the range of f
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h1 : -1 ≤ sin x := by linarith [neg_one_le_sin x]
      have h2 : sin x ≤ 1 := by linarith [sin_le_one x]
      have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      nlinarith [sq_nonneg (sin x + 1), sq_nonneg (cos x), sq_nonneg (sin x - 1)]
  · -- Show that -1 is least in range of f
    constructor
    · -- Show that -1 is in the range of f
      use (Real.pi / 2)
      rw [hf]
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h2 : cos (Real.pi / 2) = 0 := by
          have h2 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
          exact h2
      simp [h1, h2]
      all_goals linarith
    · -- Show that no smaller element is in the range of f
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h1 : -1 ≤ sin x := by linarith [neg_one_le_sin x]
      have h2 : sin x ≤ 1 := by linarith [sin_le_one x]
      have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      nlinarith [sq_nonneg (sin x - 1), sq_nonneg (cos x), sq_nonneg (sin x + 1)]