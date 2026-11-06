import Mathlib

theorem number_theory_19108 (S : ℕ → ℕ) (hS : S = fun n => ∑ i in Finset.range n, 2 ^ i):
    IsGreatest {x | ∃ n, x = Nat.gcd (S n) (S (n + 1))} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 1
    simp [hS]
  · -- Show that 1 is the greatest element in the set
    intro x hx
    rcases hx with ⟨n, hn⟩
    rw [hn]
    have h1 : ∀ n, S n = 2 ^ n - 1 := by
      intro n
      rw [hS]
      induction n with
      | zero =>
        simp
      | succ n ih =>
        simp [Finset.sum_range_succ, ih]
        all_goals
          cases n with
          | zero =>
            all_goals norm_num
          | succ n =>
            simp [Nat.pow_succ, Nat.pow_add, Nat.pow_mul]
            all_goals omega
    have h2 : Nat.gcd (S n) (S (n + 1)) = 1 := by
      rw [h1 n, h1 (n + 1)]
      have h3 : ∀ n : ℕ, (2 ^ (n + 1) - 1 : ℕ) = 2 * (2 ^ n - 1 : ℕ) + 1 := by
        intro n
        induction n with
        | zero =>
          all_goals omega
        | succ n ih =>
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, ih]
          all_goals omega
      have h4 : Nat.gcd (2 ^ n - 1 : ℕ) (2 ^ (n + 1) - 1 : ℕ) = 1 := by
        have h5 : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1 : ℕ) + 1 := by
          apply h3 n
        rw [h5]
        have h7 : Nat.gcd (2 ^ n - 1 : ℕ) (2 * (2 ^ n - 1 : ℕ) + 1) = 1 := by
          have h8 : Nat.gcd (2 ^ n - 1 : ℕ) (2 * (2 ^ n - 1 : ℕ) + 1) = Nat.gcd (2 ^ n - 1 : ℕ) 1 := by
            simp [Nat.gcd_comm, Nat.gcd_add_mul_left_right]
          rw [h8]
          simp
        exact h7
      exact h4
    have h3 : Nat.gcd (S n) (S (n + 1)) ≤ 1 := by
      rw [h2]
      all_goals omega
    linarith