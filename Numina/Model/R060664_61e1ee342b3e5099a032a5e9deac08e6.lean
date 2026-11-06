import Mathlib

def is_reversible_prime (p : ℕ) := Nat.Prime p ∧ Nat.Prime (Nat.ofDigits 10 (List.reverse (Nat.digits 10 p)))

theorem number_theory_23512 :
    IsLeast {p | 17 < p ∧ is_reversible_prime p} 31 := by
  constructor
  · constructor
    · norm_num -- Show 31 > 17
    · -- Show that 31 is a reversible prime
      unfold is_reversible_prime
      constructor
      · norm_num -- 31 is prime
      · native_decide -- Verify that reversed 31 is prime
  · -- Show 31 is minimal
    intro p hp
    rcases hp with ⟨hp1, hpr⟩
    unfold is_reversible_prime at hpr
    rcases hpr with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h1 h2 ⊢ <;> all_goals contradiction
    all_goals tauto
    all_goals contradiction