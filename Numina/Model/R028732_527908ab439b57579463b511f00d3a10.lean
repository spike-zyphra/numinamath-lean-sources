import Mathlib

noncomputable def c : ℕ → ℤ
| 0 => 2
| 1 => 3
| k + 2 => 3 * c (k + 1) - 2 * c k

noncomputable def S : ℕ → ℤ
| n => ∑ i in Finset.range n, c i

theorem algebra_248401 {S : ℕ → ℤ} (hS : ∀ n, S n = ∑ i in Finset.range n, c i) :
    (∀ n, S n = 2^n - 1 + n) ∧ (∀ n, S (n + 2) = 3 * S (n + 1) - 2 * S n - 1) := by 
  have h1 : ∀ n, S n = 2 ^ n - 1 + n := by
    intro n
    rw [hS n]
    have h2 : ∀ (n : ℕ), ∑ i in Finset.range n, c i = 2 ^ n - 1 + n := by
      intro n
      induction n with
      | zero =>
        simp [Finset.sum_range_succ, c]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have h3 : c n = 2 ^ n + 1 := by
          have h3 : ∀ (k : ℕ), c k = 2 ^ k + 1 := by
            intro k
            induction' k using Nat.strongRecOn with k ih
            cases k with
            | zero =>
              simp [c]
            | succ k =>
              cases k with
              | zero =>
                simp [c]
              | succ k =>
                have h4 : c (k + 2) = 3 * c (k + 1) - 2 * c k := by
                  simp [c]
                have h5 : c (k + 1) = 2 ^ (k + 1) + 1 := by
                  apply ih (k + 1)
                  all_goals
                    omega
                have h6 : c k = 2 ^ k + 1 := by
                  apply ih k
                  all_goals
                    omega
                rw [h4, h5, h6]
                ring_nf
          specialize h3 n
          simpa using h3
        simp [h3]
        all_goals
          ring_nf
    simpa using h2 n
  have h3 : ∀ n, S (n + 2) = 3 * S (n + 1) - 2 * S n - 1 := by
    intro n
    have h10 : S (n + 2) = 2 ^ (n + 2) - 1 + (n + 2 : ℕ) := by
      specialize h1 (n + 2)
      simpa using h1
    have h11 : S (n + 1) = 2 ^ (n + 1) - 1 + (n + 1 : ℕ) := by
      specialize h1 (n + 1)
      simpa using h1
    have h12 : S n = 2 ^ n - 1 + n := by
      specialize h1 n
      simpa using h1
    rw [h10, h11, h12]
    cases n with
    | zero =>
      all_goals
        norm_num
    | succ n =>
      simp [pow_two, pow_succ, pow_zero, Nat.mul_add, Nat.add_mul] at *
      all_goals
        ring_nf
  constructor
  · exact h1
  · exact h3