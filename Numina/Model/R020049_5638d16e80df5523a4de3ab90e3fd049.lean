import Mathlib

theorem number_theory_110835 (a : ℕ) (ha : a ≥ 2) :
    Nat.Prime (a^2 - 1) ↔ a^2 - 1 = 3 := by
  constructor
  · -- If $a^2 - 1$ is prime, then $a^2 - 1 = 3$.
    intro h
    by_cases h2 : a ≤ 2
    · -- a ≤ 2 and a ≥ 2, so a = 2
      have ha2 : a = 2 := by linarith
      have h3 : a ^ 2 - 1 = 3 := by
        rw [ha2]
        all_goals
        norm_num
      exact_mod_cast h3
    · -- a > 2
      have h3 : a ≥ 3 := by omega
      have h4 : a ≥ 3 := h3
      have h7 : a ^ 2 - 1 = (a - 1) * (a + 1) := by
        cases a with
        | zero => linarith
        | succ a =>
          cases a with
          | zero => linarith
          | succ a =>
            simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
            all_goals
            ring_nf
            <;> omega
      have h8 : a - 1 ≥ 2 := by omega
      have h9 : a + 1 ≥ 4 := by omega
      have h10 : ¬ Nat.Prime (a ^ 2 - 1) := by
        rw [h7]
        apply Nat.not_prime_mul (by nlinarith) (by nlinarith)
      contradiction
  · -- If a^2 - 1 = 3, then $a^2 - 1$ is prime.
    intro h
    have h10 : a ^ 2 = 4 := by 
      have h11 : a ^ 2 - 1 = 3 := h
      have h12 : a ^ 2 = 4 := by
        omega
      exact_mod_cast h12
    have ha2 : a = 2 := by
      nlinarith
    rw [ha2] at h
    rw [ha2]
    all_goals
    norm_num