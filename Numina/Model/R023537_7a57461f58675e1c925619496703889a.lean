import Mathlib

open Finset Real Nat

theorem algebra_191577 : ∑ i ∈ range 2000, (i + 1) / ((Nat.factorial (i + 2)) : ℝ) = 1 - 1 / (Nat.factorial 2001) := by
  have h1 : ∀ n : ℕ, ∑ i ∈ range n, (i + 1) / ((Nat.factorial (i + 2)) : ℝ) = 1 - 1 / (Nat.factorial (n + 1 : ℕ)) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> try { linarith }
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp [Nat.factorial]
      <;> ring_nf 
      <;> field_simp [Nat.factorial]
      <;> ring
  specialize h1 2000
  norm_num at h1 ⊢
  <;> try { linarith }