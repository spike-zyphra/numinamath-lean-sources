import Mathlib

theorem algebra_249435 {S1 S2 : ℕ → ℤ} (hS1 : ∀ n, S1 n = ∑ i in Finset.range n, (i * 4 + 8))
    (hS2 : ∀ n, S2 n = ∑ i in Finset.range n, (i * 2 + 17)) :
    ∃! n, n ≠ 0 ∧ S1 n = S2 n := by

  have h1 : ∀ n, S1 n = 2 * (n : ℤ) ^ 2 + 6 * (n : ℤ) := by 
    intro n 
    rw [hS1 n]
    have h : ∀ (n : ℕ), ∑ i in Finset.range n, (i * 4 + 8 : ℤ) = 2 * (n : ℤ) ^ 2 + 6 * (n : ℤ) := by 
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        <;> ring 
    specialize h n 
    simpa using h 
  have h2 : ∀ n, S2 n = (n : ℤ) ^ 2 + 16 * (n : ℤ) := by 
    intro n 
    rw [hS2 n]
    have h : ∀ (n : ℕ), ∑ i in Finset.range n, (i * 2 + 17 : ℤ) = (n : ℤ) ^ 2 + 16 * (n : ℤ) := by 
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        <;> ring 
    specialize h n 
    simpa using h 
  use 10 
  constructor
  · -- Show that 10 is indeed a solution
    constructor
    · -- Show that 10 ≠ 0 
      norm_num 
    · -- Show that S1 10 = S2 10 
      rw [h1 10, h2 10]
      all_goals norm_num 
  · -- Show that 10 is unique 
    intro n hn 
    rcases hn with ⟨hn1, hneq⟩ 
    rw [h1 n, h2 n] at hneq 
    have hneq' : (n : ℤ) * ((n : ℤ) - 10) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 hneq') with hneq1 hneq2 
    · -- hneq1: (n : ℤ) = 0 
      have hneq1' : n = 0 := by 
        norm_cast at hneq1 
      contradiction 
    · -- hneq2: (n : ℤ) - 10 = 0 
      have hneq2' : (n : ℤ) = 10 := by 
        linarith 
      have hn2 : n = 10 := by 
        norm_cast at hneq2' 
      tauto