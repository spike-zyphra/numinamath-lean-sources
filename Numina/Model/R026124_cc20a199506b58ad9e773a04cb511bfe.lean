import Mathlib

theorem number_theory_75696 (s : Finset ℕ) (h₀ : s.card = 64) (h₁ : ∀ n ∈ s, n ≤ 2012) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, 2013 ∣ a + b - c - d := by
  have h4 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h₀
    simp at h₀
  rcases h4 with ⟨x, hx⟩
  use x, by simpa using hx
  use x, by simpa using hx
  use x, by simpa using hx
  use x, by simpa using hx
  simp
  all_goals omega