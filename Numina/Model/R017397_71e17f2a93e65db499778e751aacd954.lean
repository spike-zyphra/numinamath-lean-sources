import Mathlib

open Finset

theorem algebra_310978 {F : ℕ → ℝ} (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 1)
    (hF1 : F 1 = 1) (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {x | ∃ a : ℕ → ℝ, (∀ i ∈ Icc 0 n, 0 ≤ a i) ∧ a 0 = 1 ∧ (∀ i ∈ Icc 0 (n - 2), a i ≤ a (i + 1) + a (i + 2)) ∧ x = ∑ i ∈ Icc 0 n, a i} ((F (n + 2) - 1) / F n) := by
  have h1 := hF 0
  simp at h1
  all_goals
  linarith [hF0, h1]