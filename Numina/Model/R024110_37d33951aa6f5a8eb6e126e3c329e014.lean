import Mathlib

theorem algebra_189668 (n : ℕ) :
    ∑ i in Finset.range n, (2 * i + 1) ^ 3 = n ^ 2 * (2 * n ^ 2 - 1) := by
  have h : ∀ (n : ℕ), ∑ i in Finset.range n, (2 * i + 1) ^ 3 = n ^ 2 * (2 * n ^ 2 - 1) := by
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
          <;> omega
      | succ n => 
        simp [add_mul, mul_add, pow_two, pow_succ, pow_zero] at *
        <;> ring_nf at *
        <;> omega 
  exact h n