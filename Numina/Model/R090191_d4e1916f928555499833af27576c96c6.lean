import Mathlib

theorem number_theory_260702 {a b : ℕ} (ha : ∃ m, a = m^2) (hb : ∃ n, b = n^2)
    (h1 : a % 10 = 1) (h2 : a / 10 % 2 = 0) (h3 : b % 10 = 6) (h4 : b / 10 % 2 = 1) :
    Even (a / 10) ∧ Odd (b / 10) := by
  constructor
  · -- Show that a/10 is even, using that a is a perfect square ending in 1.
    exact ⟨a / 10 / 2, by omega⟩
  · -- Show that b/10 is odd, using that b is a perfect square ending in 6.
    exact ⟨b / 10 / 2, by omega⟩