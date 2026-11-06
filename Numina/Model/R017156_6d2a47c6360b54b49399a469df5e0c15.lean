import Mathlib

theorem number_theory_2171 (n : ℕ) (f : ℕ → ℕ) (hf : ∀ n, f n = n ^ 7 - n ^ 4 + n ^ 2 + n + 1)
    (hn : Nat.Prime (f n)) : n = 1 := by
  have h1 : f n = n ^ 7 - n ^ 4 + n ^ 2 + n + 1 := hf n
  rw [h1] at hn
  by_cases h : n > 1
  · -- Assume n > 1
    have h2 : n ^ 7 - n ^ 4 + n ^ 2 + n + 1 = (n ^ 4 * (n - 1) + 1) * (n ^ 2 + n + 1) := by
      cases n with
      | zero =>
        omega
      | succ n =>
        cases n with
        | zero =>
          omega
        | succ n =>
          simp [Nat.mul_sub_left_distrib, Nat.sub_eq_zero_iff_le, pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          <;> ring_nf <;> omega
    rw [h2] at hn
    have h4 : n ^ 4 * (n - 1) + 1 > 1 := by
      have h9 : n ≥ 2 := by omega
      have h9' : n - 1 ≥ 1 := by omega
      have h9'' : n ^ 4 ≥ 16 := by
        have : n ≥ 2 := by omega
        have h6 : n ^ 4 ≥ 2 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        have h7 : 2 ^ 4 = 16 := by norm_num
        linarith [h6, h7]
      have h9''' : n ^ 4 * (n - 1) ≥ 16 := by
        nlinarith [h9', h9'']
      omega
    have h5 : n ^ 2 + n + 1 > 1 := by
      have h6 : n ≥ 2 := by omega
      nlinarith
    -- Now, the product of two numbers > 1 is not prime
    have h7 : ¬ Nat.Prime ((n ^ 4 * (n - 1) + 1) * (n ^ 2 + n + 1)) := by
      apply Nat.not_prime_mul
      all_goals
        linarith [h4, h5]
    contradiction
  · -- Assume n ≤ 1
    have h4 : n ≤ 1 := by omega
    interval_cases n <;> norm_num [hf] at hn ⊢ <;> try tauto