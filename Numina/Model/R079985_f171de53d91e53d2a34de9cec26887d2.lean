import Mathlib

theorem number_theory_235728 (a : ℕ → ℤ)
    (h₀ : a 0 = 1)
    (h₁ : a 1 = 2)
    (h₂ : ∀ n, a (n + 1) = ∑ i in Finset.range (n + 1), a i) :
    ¬∃ n, a n = 72 := by 
  intro h
  rcases h with ⟨n, hn⟩
  have h₃ := h₂ 0
  simp [Finset.sum_range_succ, h₀] at h₃ 
  all_goals 
    linarith [h₃, h₁]