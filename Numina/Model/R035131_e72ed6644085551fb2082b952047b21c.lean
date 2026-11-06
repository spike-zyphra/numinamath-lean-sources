import Mathlib

theorem number_theory_218881 (n : ℕ) (hn : n > 2) :
    (n^3 + 3) % (n + 1) = 2 := by
  have h1 : n ≥ 3 := by linarith
  have h3 : n ^ 3 + 3 = (n + 1) * (n^2 - n + 1) + 2 := by
    cases n with
    | zero => linarith
    | succ n =>
      cases n with
      | zero => linarith
      | succ n =>
        cases n with
        | zero => linarith
        | succ n => 
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          <;> ring_nf
          <;> omega
  rw [h3]
  simp [Nat.add_mod, Nat.mul_mod]
  <;> omega