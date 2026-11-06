import Mathlib

theorem number_theorey_4859 (p a : ℕ) [hp : Fact (Nat.Prime p)] (ha : 1 ≤ a):
    (p ^ a).totient = p ^ a - p ^ (a - 1) := by 
  have h1 : Nat.Prime p := hp.1
  have h2 : 0 < a := by linarith
  have h3 : (p ^ a).totient = p ^ (a - 1) * (p - 1) := by 
    rw [Nat.totient_prime_pow]
    all_goals 
      try exact h1
      try exact h2
  calc
    (p ^ a).totient = p ^ (a - 1) * (p - 1) := h3
    _ = p ^ a - p ^ (a - 1) := by 
      cases a with
      | zero => linarith
      | succ n => 
        cases n with
        | zero => 
          simp
        | succ n => 
          simp [Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.sub_eq_zero_of_le] at *
          <;> ring_nf
          <;> omega