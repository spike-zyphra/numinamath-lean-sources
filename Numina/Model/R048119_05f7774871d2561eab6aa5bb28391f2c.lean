import Mathlib

theorem number_theory_125185 (s : Finset ℤ) (h₀ : s.card = 10)
    (h₁ : {d | ∃ a ∈ s, ∃ b ∈ s, d = max a b - min a b}.encard = 44) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a = (b + c) / 2 := by 
  have h2 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.2
    by_contra h
    rw [h] at h₀
    simp at h₀
    all_goals linarith
  rcases h2 with ⟨a, ha⟩
  use a, by exact ha
  use a, by exact ha
  use a, by exact ha
  all_goals omega