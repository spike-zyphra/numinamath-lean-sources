import Mathlib

theorem algebra_98080 (a d n : ℕ) (h₀ : d ≠ 0) (h₁ : n > 0) :
    ∑ i ∈ Finset.range (3 * n), (a + d * i) - ∑ i ∈ Finset.range (2 * n), (a + d * i) -
    ∑ i ∈ Finset.range n, (a + d * i) = 2 * d * n ^ 2 := by
  have h2 : ∀ m : ℕ, ∑ i ∈ Finset.range m, (a + d * i) = m * a + (d * (m - 1) * m) / 2 := by
    intro m
    induction' m with m ih 
    · 
      simp
      <;> ring_nf <;> omega
    · 
      rw [Finset.sum_range_succ, ih]
      cases m with
      | zero => 
        simp 
        <;> ring_nf <;> omega
      | succ m => 
        simp [Nat.mul_add, Nat.add_mul, pow_two]
        <;> ring_nf <;> omega 
  rw [h2 (3 * n), h2 (2 * n), h2 n]
  cases n with
  | zero => 
    linarith
  | succ n => 
    simp [Nat.mul_add, Nat.add_mul]
    <;> ring_nf <;> omega