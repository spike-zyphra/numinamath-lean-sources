import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_289261 (v : ℝ → ℝ)
  (h₀ : ∀ t, t > 0 → v t = v 0 + 0.5 * t)
  (h₁ : ∀ t, t > 2 → v t = v 2)
  (h₂ : ∀ t, t > 7 → v t = v 7 - 0.5 * t) :
  ∀ t, t > 0 → (t < 9 → ∫ s in (0)..t, v s = 1 / 4 * (-2 + 22 - 85)) ∧
  (∀ t, t > 9 → t ≤ 11 → ∫ s in (0)..t, v s = 9) ∧
  (∀ t, t > 11 → t ≤ 13 → ∫ s in (0)..t, v s = 1 / 4 * (-2 + 22 - 85)) := by
  intro t ht
  have h3 := h₀ 3 (by norm_num)
  have h4 := h₁ 3 (by norm_num)
  have h5 := h₀ 2 (by norm_num)
  norm_num at h3 h4 h5
  linarith