import Mathlib

/- Find the smallest positive integer that is greater than $1$ and relatively prime to the product of the first 20 positive integers.  Reminder: two numbers are relatively prime if their greatest common divisor is 1. -/
theorem algebra_21465 :
    IsLeast {n | 0 < n ∧ n > 1 ∧ Nat.Coprime n (∏ i ∈ Finset.range 20, (i + 1))} 23 := by
  constructor
  · -- $23$ is relatively prime to the product of the first 20 positive integers
    simp only [gt_iff_lt, Finset.prod_range_add_one_eq_factorial, Set.mem_setOf_eq, Nat.ofNat_pos, Nat.one_lt_ofNat, true_and]
    exact rfl
  -- $23$ is the least such integer
  intro n nin
  simp only [gt_iff_lt, Finset.prod_range_add_one_eq_factorial, Set.mem_setOf_eq] at nin
  rcases nin with ⟨_, ngt, hn⟩
  by_contra contra
  rw [not_le] at contra
  interval_cases n
  all_goals
  exact (Nat.one_mod_eq_one.mp rfl) hn