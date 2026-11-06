import Mathlib

theorem number_theory_111371 (s : Finset ℝ) (h₀ : s.card = 3) (h₁ : ∀ x ∈ s, x ∈ Set.Ico 0 1) :
    ∃ a ∈ s, ∃ b ∈ s, |b - a| < 1 / 2 := by
  have h_nonempty : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h₀
    simp at h₀
  rcases h_nonempty with ⟨a, ha⟩
  use a, ha
  use a, ha
  simp
  all_goals linarith