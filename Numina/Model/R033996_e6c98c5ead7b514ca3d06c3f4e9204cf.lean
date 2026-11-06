import Mathlib

open Real Set
open scoped Real

theorem inequalities_5656 :
  IsLeast {a : ℕ | 0 < a ∧ ∀ x : ℝ, sin x ^ 2 + a * cos x + a ^ 2 > 1 + cos x} 2 := by
  constructor
  · -- Show 2 is in the set
    constructor
    · norm_num
    · intro x
      have h1 : sin x ^ 2 + (2 : ℕ) * cos x + (2 : ℕ) ^ 2 > 1 + cos x := by
        norm_num
        have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by
          have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          linarith
        rw [h2]
        nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), Real.cos_le_one x, Real.neg_one_le_cos x]
      simpa using h1
  · -- Show that no smaller element is in the set
    intro a ha
    rcases ha with ⟨ha_pos, h⟩
    by_contra h2
    push_neg at h2
    have h3 : a = 1 := by
      have h4 : a < 2 := by linarith
      have h5 : a = 1 := by
        interval_cases a <;> omega
      exact h5
    rw [h3] at h
    have h4 := h 0
    norm_num [Real.sin_zero, Real.cos_zero] at h4
    all_goals linarith