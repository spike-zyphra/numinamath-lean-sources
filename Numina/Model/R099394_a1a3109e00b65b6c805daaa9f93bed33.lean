import Mathlib

def S : ℕ → ℤ
| n => ∑ k in Finset.range (n + 1), k ^ 2

theorem algebra_216733 (n : ℕ) : S n = n * (n + 1) * (2 * n + 1) / 6 := by 
  rw [S]
  have h1 : ∀ n : ℕ, (∑ k in Finset.range (n + 1), (k : ℤ) ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by 
    intro n
    induction n with
    | zero =>
      simp 
    | succ n ihN =>
      rw [Finset.sum_range_succ]
      -- Substitute the induction hypothesis for the sum up to n
      rw [ihN]
      simp [add_mul, mul_add, pow_two]
      ring_nf at *
      <;> omega 
  specialize h1 n 
  simpa using h1 
  <;> try { linarith }
  <;> try { ring_nf at * <;> omega }
  all_goals try { linarith }
  all_goals try { ring_nf at * <;> omega }