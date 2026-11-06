import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12455 {k : ℤ} (x : ℝ) :
  x ∈ {x | ∃ k : ℤ, x = (7/6)*π + 2*k*π ∨ x = (5/6)*π + 2*k*π} ↔
  x ∈ {x | ∃ k : ℤ, x = (7/6)*π + 2*k*π ∨ x = -(7/6)*π + 2*k*π} := by

  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume x ∈ M
    intro h
    rcases h with ⟨k, h⟩
    rcases h with (h | h)
    · -- Case x = (7/6)*π + 2*k*π
      refine ⟨k, ?_⟩
      left
      simpa using h
    · -- Case x = (5/6)*π + 2*k*π
      refine ⟨k + 1, ?_⟩
      right
      field_simp at h ⊢
      <;> ring_nf at h ⊢ <;> linarith [h]
  · -- Assume x ∈ N
    intro h
    rcases h with ⟨k, h⟩
    rcases h with (h | h)
    · -- Case x = (7/6)*π + 2*k*π
      refine ⟨k, ?_⟩
      left
      simpa using h
    · -- Case x = -(7/6)*π + 2*k*π
      refine ⟨k - 1, ?_⟩
      right
      field_simp at h ⊢
      <;> ring_nf at h ⊢ <;> linarith [h]