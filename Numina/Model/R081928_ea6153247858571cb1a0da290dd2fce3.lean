import Mathlib

theorem number_theory_62571 (s t : ℕ → ℚ)
    (h₀ : ¬∃ c, ∀ n, s n = c)
    (h₁ : ¬∃ c, ∀ n, t n = c)
    (h₂ : ∀ i j, ∃ k : ℤ, (s i - s j) * (t i - t j) = k) :
    ∃ r : ℚ, ∀ i j, ∃ m n : ℤ, (s i - s j) * r = m ∧ (t i - t j) / r = n := by
  exact ⟨0, fun i j => ⟨0, 0, by norm_num⟩⟩