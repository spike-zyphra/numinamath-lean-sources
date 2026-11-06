import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_150088 {x : ℝ} :
  x ∈ {x | ∃ k : ℤ, x = 7 / 6 * π + 2 * k * π ∨ x = 5 / 6 * π + 2 * k * π} ↔
  x ∈ {x | ∃ k : ℤ, x = 7 / 6 * π + 2 * k * π ∨ x = -7 / 6 * π + 2 * k * π} := by 
  apply Iff.intro 
  · -- Prove the forward direction: if x ∈ M, then x ∈ N 
    rintro ⟨k, hk⟩ 
    rcases hk with (h | h)
    · -- Case where x = 7/6 * π + 2k * π 
      refine ⟨k, ?_⟩ 
      left 
      exact h 
    · -- Case where x = 5/6 * π + 2k * π 
      refine ⟨k + 1, ?_⟩ 
      right 
      field_simp at h ⊢ 
      linarith 
  · -- Prove the reverse direction: if x ∈ N, then x ∈ M 
    rintro ⟨k, hk⟩ 
    rcases hk with (h | h)
    · -- Case where x = 7/6 * π + 2k * π 
      refine ⟨k, ?_⟩ 
      left 
      exact h 
    · -- Case where x = -7/6 * π + 2k * π 
      refine ⟨k - 1, ?_⟩ 
      right 
      field_simp at h ⊢ 
      linarith