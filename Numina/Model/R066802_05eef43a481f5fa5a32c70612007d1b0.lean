import Mathlib

theorem number_theory_177506 :
    {n : ℕ | n < 50 ∧ Nat.gcd (4 * n + 5) (7 * n + 6) > 1} = {7, 18, 29, 40} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if $n < 50$ and $\gcd(4n+5, 7n+6) > 1$, then $n \in \{7, 18, 29, 40\}$.
    intro h
    rcases h with ⟨h1, h2⟩
    interval_cases n <;> norm_num at *
  · -- Backward direction: if $n \in \{7, 18, 29, 40\}$, then $n < 50$ and $\gcd(4n+5, 7n+6) > 1$.
    rintro (rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      · norm_num [Nat.gcd]
    · constructor
      · norm_num
      · norm_num [Nat.gcd]
    · constructor
      · norm_num
      · norm_num [Nat.gcd]
    · constructor
      · norm_num
      · norm_num [Nat.gcd]