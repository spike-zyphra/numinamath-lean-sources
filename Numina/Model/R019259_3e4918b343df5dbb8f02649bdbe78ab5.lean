import Mathlib

theorem algebra_318816 (n : ℕ) :
    ∑ i in Finset.range n, (2 * i + 1) ^ 2 = n * (4 * n ^ 2 - 1) / 3 := by 
  have h1 : ∀ n : ℕ, ∑ i in Finset.range n, (2 * i + 1) ^ 2 = n * (4 * n ^ 2 - 1) / 3 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      cases n with
      | zero =>
        all_goals
          simp
      | succ n =>
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.pow_two] at ih ⊢
        <;> ring_nf at ih ⊢ 
        <;> omega 
  exact h1 n