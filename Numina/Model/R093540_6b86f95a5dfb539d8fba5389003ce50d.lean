import Mathlib

theorem number_theory_42687 (a : ℕ) (ha : a < 10) (h : 2012 ∈ {x | ∃ n, x = a + 9 * n}) :
    a = 5 := by
  simp at h
  rcases h with ⟨n, hn⟩
  omega