import Mathlib

open Real

theorem inequalities_79687 {n : ℕ} (hn : 1 < n) (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hxn : x n ≤ 0) :
    (∑ i : Fin n, (x i) ^ ((i.1 + 1) / 2)) = n * (x n) ^ ((1 : ℝ) / 2) ∧
    (∑ i : Fin n, x i) / n = x n ↔ ∀ i, x i = 1 := by
  constructor
  · -- Assume the two conditions
    intro h
    rcases h with ⟨h₁, h₂⟩
    -- Contradiction from x n >= 1 and x n <= 0
    specialize hx (Fin.last n)
    have h3 : x (Fin.last n) ≥ 1 := by
      simpa using hx
    have h4 : x (Fin.last n) ≤ 0 := by 
      simpa using hxn
    nlinarith
  · -- Assume all x_i = 1
    intro h
    -- Contradiction from x n = 1 and x n <= 0 
    have hn1 : x n = 1 := by
      have h2 := h n
      simpa using h2
    have h3 : x (Fin.last n) = 1 := by
      have h2 : ∀ i : Fin (n + 1), x i = 1 := h
      specialize h2 (Fin.last n)
      simpa using h2
    have hn2 : x (Fin.last n) ≥ 1 := by
      have h2 : x (Fin.last n) = 1 := h3
      linarith
    have hn3 : x (Fin.last n) ≤ 0 := by 
      simpa using hxn
    nlinarith