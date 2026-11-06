import Mathlib

theorem number_theory_8870 (g : ℕ → ℕ) (hg1 : g 1 = 1) (hxn : ∀ n > 0, g (n + 1) = g n ^ 2 + g n + 1) :
    ∀ n > 0, (g n) ^ 2 + 1 ∣ (g (n + 1)) ^ 2 + 1 := by 
  intro n hn
  have h2 : g (n + 1) = g n ^ 2 + g n + 1 := hxn (n) hn
  rw [h2]
  use (g n) ^ 2 + 2 * (g n) + 2
  ring_nf
  <;> omega