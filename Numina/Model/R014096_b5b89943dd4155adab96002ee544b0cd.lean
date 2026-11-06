import Mathlib

theorem algebra_192586 (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) ^ 3 = n ^ 2 * (2 * n ^ 2 - 1) := by 
  have h1 : ∀ (n : ℕ), ∑ i in Finset.range n, (2 * i + 1) ^ 3 = n ^ 2 * (2 * n ^ 2 - 1) := by
    intro n 
    induction n with
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      cases n with
      | zero =>
        simp [Nat.pow_succ, Nat.mul_assoc] 
        <;> omega 
      | succ n =>
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, mul_add, add_mul, pow_two, pow_succ, Nat.mul_assoc] at *
        <;> ring_nf 
        <;> omega 
  specialize h1 n
  simpa using h1