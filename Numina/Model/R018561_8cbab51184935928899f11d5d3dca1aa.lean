import Mathlib

theorem number_theory_82683 (s : Finset ℕ) (h₀ : s.card = 101)
    (h₁ : ∀ n ∈ s, n < 5050) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, 5050 ∣ a + b - c - d := by

  have h2 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.2
    by_contra h
    rw [h] at h₀
    simp at h₀

  rcases h2 with ⟨x, hx⟩

  -- Let us pick the same element four times
  use x, hx
  use x, hx
  use x, hx
  use x, hx

  all_goals
    -- Show that 5050 divides x + x - x - x = 0
    norm_num