import Mathlib

theorem number_theory_199592 {n : ℕ} (hn : n % 2 = 1 ∧ n % 3 = 1) :
    n % 4 = 3 ∧ n % 5 = 3 → n % 12 = 7 := by
  intro h
  have h1 : n % 2 = 1 := hn.1
  have h2 : n % 3 = 1 := hn.2
  have h3 : n % 4 = 3 := h.1
  have h4 : n % 5 = 3 := h.2
  omega