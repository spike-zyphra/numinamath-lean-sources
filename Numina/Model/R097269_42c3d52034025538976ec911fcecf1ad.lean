import Mathlib

theorem number_theory_257321 (n : ℤ) :
    IsSquare (7 * n + 2) ↔ ∃ k, 7 * n + 2 = k ^ 2 := by 
  apply Iff.intro 
  · -- Assume (7 * n + 2) is a square, prove ∃ k, 7 * n + 2 = k ^ 2
    intro h
    rcases h with ⟨k, hk⟩ 
    -- Since IsSquare (7 * n + 2) is equivalent to ∃ k, (k : ℤ) ^ 2 = 7 * n + 2 
    exact ⟨k, by linarith [hk]⟩

  · -- Assume ∃ k, 7 * n + 2 = k ^ 2, prove IsSquare (7 * n + 2) 
    intro h 
    rcases h with ⟨k, hk⟩ 
    -- From existence of k such that 7n+2 = k^2, conclude IsSquare 
    exact ⟨k, by linarith [hk]⟩