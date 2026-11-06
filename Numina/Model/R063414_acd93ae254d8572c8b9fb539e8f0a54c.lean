import Mathlib

theorem algebra_128225 {n : ℕ} (hn : n > 20 ∧ n < 30)
    (h : ∃ f m : ℕ, f = 2 * m ∧ f + m = n) (h' : ∃ s : ℕ, s = 3 * (n - s) - 1) :
    n = 27 := by

  rcases hn with ⟨hn1, hn2⟩
  rcases h with ⟨f, m, h1, h2⟩
  have h3 : n = 3 * m := by
    omega
  rcases h' with ⟨s, h4⟩
  have h5 : n ≥ 21 := by omega
  have h6 : n ≤ 29 := by omega
  interval_cases n <;> try { 
    omega 
  } <;> omega