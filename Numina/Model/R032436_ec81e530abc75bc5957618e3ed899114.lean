import Mathlib

open Finset

theorem algebra_160868 {F : ℕ → ℝ} (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 1)
    (hF1 : F 1 = 1) (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {∑ i ∈ range (n + 1), a i | (a : ℕ → ℝ) (ha : ∀ i ∈ range (n + 1), 0 ≤ a i)
      (h0 : a 0 = 1) (h1 : ∀ i ∈ range (n - 1), a i ≤ a (i + 1) + a (i + 2))} ((F (n + 2) - 1) / F n) := by

  have h2 := hF 0
  simp at h2
  all_goals linarith [hF0]