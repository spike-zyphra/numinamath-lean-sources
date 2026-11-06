import Mathlib

theorem algebra_94721 {s1 s2 : ℕ → ℤ}
    (h1 : ∀ n, s1 n = ∑ i in Finset.range n, (i * 4 + 8))
    (h2 : ∀ n, s2 n = ∑ i in Finset.range n, (i * 2 + 17)) :
    ∃! n, s1 n = s2 n ∧ n ≠ 0 := by
  have eq1 : ∀ n, s1 n = 2 * (n : ℤ) ^ 2 + 6 * (n : ℤ) := by
    intro n 
    rw [h1 n]
    have eq3 : ∀ n : ℕ, (∑ i in Finset.range n, (i * 4 + 8 : ℕ) : ℤ) = 2 * (n : ℤ) ^ 2 + 6 * (n : ℤ) := by
      intro n 
      induction n with 
      | zero =>
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih]
        simp [mul_add, add_mul, add_assoc]
        <;> ring_nf
        <;> omega
    specialize eq3 n
    simpa using eq3

  have eq2 : ∀ n, s2 n = (n : ℤ) ^ 2 + 16 * (n : ℤ) := by
    intro n 
    rw [h2 n]
    have eq3 : ∀ n : ℕ, (∑ i in Finset.range n, (i * 2 + 17 : ℕ) : ℤ) = (n : ℤ) ^ 2 + 16 * (n : ℤ) := by
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih] 
        simp [mul_add, add_mul, add_assoc]
        <;> ring_nf 
        <;> omega 
    specialize eq3 n
    simpa using eq3 
  use 10
  constructor
  · -- Show that 10 is indeed a solution
    constructor
    · -- Show that s1 10 = s2 10
      rw [eq1 10, eq2 10]
      norm_num 
    · -- Show that 10 ≠ 0 
      norm_num
  · -- Show that for any n such that s1 n = s2 n and n ≠ 0, n = 10 
    intro n hn 
    rcases hn with ⟨h_eq, hnne0⟩ 
    rw [eq1 n, eq2 n] at h_eq 
    have eq3 : (n : ℤ) * ((n : ℤ) - 10) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp eq3) with h4 h5 
    · -- Case where n = 0 
      have : (n : ℤ) = 0 := h4 
      have hn0 : n = 0 := by 
        norm_cast at this 
      exfalso 
      apply hnne0 
      exact_mod_cast hn0
    · -- Case where n - 10 = 0 
      have h7 : (n : ℤ) = 10 := by linarith 
      have hn10 : n = 10 := by 
        norm_cast at h7 
      exact_mod_cast hn10