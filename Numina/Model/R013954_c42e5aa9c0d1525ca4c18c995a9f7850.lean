import Mathlib

theorem number_theory_57760 (S : Finset ℚ) (hS : S.card = 97)
    (hS1 : ∀ x ∈ S, ∃ n : ℕ, x = 49 / n) :
    S.card = 1 → ∃ x ∈ S, x = 1 := by
  intro h
  have h1 : S.card = 97 := hS
  have h2 : S.card = 1 := h
  rw [h1] at h2
  all_goals
    norm_num at h2