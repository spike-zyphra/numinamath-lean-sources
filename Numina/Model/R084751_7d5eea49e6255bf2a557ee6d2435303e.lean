import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303747 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = x^2 / 4 - y^2) :
  IsGreatest {z | ∃ x y, x^2 + y^2 ≤ 4 ∧ f x y = z} 1 ∧
  IsLeast {z | ∃ x y, x^2 + y^2 ≤ 4 ∧ f x y = z} (-4) := by

  constructor
  · -- vessel $vessel\_1$ is reactor
    constructor
    · -- (2, 0) is in the set and satisfies f = 1
      use 2, 0
      norm_num [h₀]
    · -- We need to show that for any z in the set, z ≤ 1
      intro z h
      rcases h with ⟨x, y, h1, h2⟩
      have h3 : f x y = z := h2
      rw [h₀] at h3
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg y]

  · -- Now proving that -4 is the least element
    constructor
    · -- (0, 2) in the set with f = -4
      use 0, 2
      norm_num [h₀]
    · -- show that -4 is minimal
      intro z h
      rcases h with ⟨x, y, h1, h2⟩
      have h3 : f x y = z := h2
      rw [h₀] at h3
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg y]