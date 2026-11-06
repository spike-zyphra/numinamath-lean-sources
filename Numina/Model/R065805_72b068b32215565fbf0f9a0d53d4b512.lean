import Mathlib

theorem number_theory_108264 (a : ℕ → ℤ) (h₀ : a 0 = 3) (h₁ : a 1 = 5 - 3)
    (h₂ : a 2 = 9 - 5) :
    ¬∃ r, ∀ n, a (n + 1) = r * a n := by
  rintro ⟨r, hr⟩
  have h1 := hr 0
  have h2 := hr 1
  simp [h₀, h₁] at h1
  simp [h₁, h₂] at h2
  omega