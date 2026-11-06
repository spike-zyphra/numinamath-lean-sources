import Mathlib

theorem number_theory_277880
    (a b : ℤ)
    (h₀ : Odd a)
    (h₁ : Odd b) :
    Even (a + b) ∧ Even (a - b) ∧ Odd (a * b) := by
  rcases h₀ with ⟨k, hk⟩
  rcases h₁ with ⟨m, hm⟩
  constructor
  · -- Show that a + b is even
    use k + m + 1
    rw [hk, hm]
    ring_nf
  constructor
  · -- Show that a - b is even
    use k - m
    rw [hk, hm]
    ring_nf
  · -- Show that a * b is odd
    use 2 * k * m + k + m
    rw [hk, hm]
    ring_nf