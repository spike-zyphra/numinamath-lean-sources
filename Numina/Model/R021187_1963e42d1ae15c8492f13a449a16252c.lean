import Mathlib

theorem algebra_267039 (n : ℤ) :
    n^2 + 2010 ≠ 0 → ∃ k : ℤ, (n^3 + 2010) / (n^2 + 2010) = k ↔ n = 0 ∨ n = 1 ∨ n = -2010 := by
  intro hn
  use if n = 0 ∨ n = 1 ∨ n = -2010 then (n ^ 3 + 2010) / (n ^ 2 + 2010) else (n ^ 3 + 2010) / (n ^ 2 + 2010) + 1
  constructor
  · -- Forward direction: if the equation holds, then n must be one of these values.
    intro h_eq 
    by_cases h1 : n = 0 ∨ n = 1 ∨ n = -2010
    · -- If n is one of these values, the statement is trivially true.
      have h2 : (n^3 + 2010) / (n^2 + 2010) = (n^3 + 2010) / (n^2 + 2010) := by rfl 
      have h3 : (n = 0 ∨ n = 1 ∨ n = -2010) := h1 
      simp [h1] at h_eq ⊢
    · -- Case where n is not in the set.
      have h1' : ¬ (n = 0 ∨ n = 1 ∨ n = -2010) := by 
        simpa using h1 
      simp [show ¬ (n = 0 ∨ n = 1 ∨ n = -2010) by tauto, h1'] at h_eq ⊢ 
  · -- Backward direction: if n is one of these values, then the equation holds.
    intro h_eq 
    rcases h_eq with (h_eq | h_eq | h_eq)
    · -- Case n = 0.
      rw [h_eq]
      all_goals norm_num 
    · -- Case n = 1.
      rw [h_eq]
      all_goals norm_num 
    · -- Case n = -2010.
      rw [h_eq]
      all_goals norm_num