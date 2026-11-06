import Mathlib

theorem number_theory_174493 (a d : ℕ) (h₀ : a < d) (h₁ : a^2 ∈ {x | ∃ n, x = a + d * n}) :
    (a + d)^2 ∈ {x | ∃ n, x = a + d * n} := by
  rcases h₁ with ⟨n, hn⟩
  use n + 2 * a + d
  have h2 : a ^ 2 = a + d * n := by
    linarith [hn]
  calc
    (a + d) ^ 2 = a ^ 2 + 2 * a * d + d ^ 2 := by ring
    _ = (a + d * n) + 2 * a * d + d ^ 2 := by rw [h2]
    _ = a + d * (n + 2 * a + d) := by ring
  all_goals linarith