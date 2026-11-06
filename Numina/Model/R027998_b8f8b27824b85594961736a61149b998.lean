import Mathlib

theorem number_theory_7940 (x y : ℤ) :
    5 * x + 13 * y = 11 ↔ ∃ n : ℤ, (x, y) = (13 * n + 10, -5 * n - 3) := by
  constructor
  · -- Assume 5x + 13y = 11, prove ∃ n, (x, y) = (13n + 10, -5n - 3)
    rintro h
    have h1 : x % 13 = 10 % 13 := by
      omega
    have h2 : ∃ n : ℤ, x = 13 * n + 10 := by
      refine' ⟨x / 13, ?_⟩
      omega
    rcases h2 with ⟨n, hn⟩
    use n
    simp [hn]
    -- Now need to prove that y = -5n - 3
    have eq1 : 5 * x + 13 * y = 11 := h
    rw [hn] at eq1
    have eq2 : y = -5 * n - 3 := by
      linarith
    simp [hn, eq2]
  · -- Assume ∃ n, (x, y) = (13n + 10, -5n - 3), prove 5x + 13y = 11
    rintro ⟨n, h⟩
    rcases h with ⟨rfl, rfl⟩
    all_goals
      ring