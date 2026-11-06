import Mathlib

theorem number_theory_69452 :
    IsLeast {b : ℕ | ∃ a : ℕ, a > 0 ∧ a < 391 ∧ Nat.lcm a b > Nat.lcm a 391} 18 := by
  constructor
  · -- Show that 18 is in the set. We verify that (a, b) = (23, 18) is a valid pair.
    use 23
    all_goals norm_num
  · -- Show that b >= 18 for all b in the set.
    intro b
    intro h
    rcases h with ⟨a, ha1, ha2, h⟩
    by_contra h1
    push_neg at h1
    interval_cases b <;> try { 
      have h1 : a ≤ 390 := by linarith
      interval_cases a <;> norm_num [Nat.lcm] at h ⊢ <;> omega
    }