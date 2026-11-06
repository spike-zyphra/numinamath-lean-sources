import Mathlib

/-Let $k$ be a positive integer. Determine the largest among the numbers $2^{5k}$, $3^{4k}$, $4^{3k}$, $5^{2k}$, and $6^{k}$. Show that this number is $3^{4k}$..-/
theorem number_theory_639910 {k : ℕ} (hk : 0 < k) : IsGreatest {2^(5*k), 3^(4*k), 4^(3*k), 5^(2*k), 6^k} (3^(4*k)) := by
  constructor
  · simp
  · intro x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, pow_mul, Nat.reducePow]
    rintro (rfl | rfl | rfl | rfl | rfl)
    all_goals
    · apply Nat.pow_le_pow_left ?_ k
      norm_num
