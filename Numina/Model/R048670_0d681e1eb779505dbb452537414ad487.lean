import Mathlib

theorem number_theory_79051 (g : ℕ → ℕ) (hg : ∀ n, 0 < g n)
    (h1 : g 1 = 1) (h2 : ∀ n, g (n + 1) = (g n)^2 + g n + 1) :
    ∀ n, 0 < n → (g n)^2 + 1 ∣ (g (n + 1))^2 + 1 := by
  intro n hn
  have h1' : g (n + 1) = (g n) ^ 2 + g n + 1 := h2 n
  rw [h1']
  use (g n) ^ 2 + 2 * (g n) + 2
  ring_nf
  <;> omega