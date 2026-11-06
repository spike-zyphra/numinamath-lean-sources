import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_94916 (u : ℕ → ℝ)
  (h₀ : u 0 = 1 / 4)
  (h₁ : ∀ k, u (k + 1) = 2 * u k - 2 * (u k)^2) :
  IsLeast {k | |u k - (1 / 2)| ≤ 1 / 2^1000} 10 := by
  constructor
  · -- Show that 10 is in the set
    norm_num [abs_le, h₀, h₁]
    all_goals norm_num
  · -- Show that any element in the set is at least 10
    intro k hk
    have h4 : |u k - (1 / 2)| ≤ 1 / 2^1000 := by
      simpa using hk
    by_contra h
    push_neg at h
    have h5 : k < 10 := by linarith
    interval_cases k <;> norm_num [abs_le, h₀, h₁] at h4 ⊢
    all_goals norm_num at h4 ⊢
    all_goals try { linarith }