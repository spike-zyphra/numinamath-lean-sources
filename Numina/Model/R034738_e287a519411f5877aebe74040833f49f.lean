import Mathlib

theorem number_theory_19544 : 
    IsGreatest {p | p.Prime ∧ p ∣ ∑ i ∈ Finset.range 9, (2 ^ i)} 73 := by
  constructor
  · -- Show that 73 is in the set.
    constructor
    · -- Show that 73 is prime.
      norm_num
    · -- Show that 73 divides the sum.
      native_decide
  · -- Show that 73 is greatest in the set.
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    have hsum : ∑ i in Finset.range 9, (2 : ℕ) ^ i = 511 := by
      norm_num [Finset.sum_range_succ]
    rw [hsum] at hdiv
    -- $p$ divides 511.
    have h1 : p ≤ 511 := by
      exact Nat.le_of_dvd (by norm_num) hdiv
    by_contra h
    push_neg at h
    -- We need to show that if $p > 73$ and $p$ is prime, then $p$ does not divide 511.
    interval_cases p <;> norm_num at h_prime hdiv <;> contradiction