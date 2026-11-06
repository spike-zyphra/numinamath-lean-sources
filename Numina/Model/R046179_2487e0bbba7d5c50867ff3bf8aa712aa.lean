import Mathlib

theorem number_theory_254750 (n : ℕ) :
    n^3 - n = Nat.factorial n ↔ n = 5 := by
  constructor
  · -- Forward implication: if n^3 - n = n! then n = 5
    intro h_eq
    by_cases h1 : n ≤ 6
    · -- n ≤ 6
      interval_cases n <;> try { simp [Nat.factorial] at h_eq <;> omega }
    · -- n > 6
      have h2 : n ≥ 7 := by omega
      have h3 : ∀ (k : ℕ), k ≥ 7 → Nat.factorial k > (k ^ 3 - k: ℕ) := by
        intro k hk
        have base7 : Nat.factorial 7 > (7 ^ 3 - 7: ℕ) := by
          norm_num [Nat.factorial]
        have step : ∀ (m : ℕ), m ≥ 7 → Nat.factorial m > (m ^ 3 - m: ℕ) → Nat.factorial (m + 1) > ((m + 1) ^ 3 - (m + 1) : ℕ) := by
          intros m hm h
          have eq1 : Nat.factorial (m + 1) = (m + 1) * (Nat.factorial m) := by
            simp [Nat.factorial]
            <;> ring_nf <;> omega
          rw [eq1]
          have eq2 : (m + 1) * (Nat.factorial m) > (m + 1) * (m ^ 3 - m) := by
            apply Nat.mul_lt_mul_of_pos_left
            omega
            all_goals
              omega
          have eq3 : (m + 1) * (m ^ 3 - m) ≥ ((m + 1) ^ 3 - (m + 1) : ℕ) := by
            have h4 : m ^ 3 - m ≥ m^2 + 2 * m := by
              have h5 : m ^ 3 ≥ (m^2 + 2 * m + m) := by
                nlinarith [sq_nonneg (m - 2 : ℤ), sq_nonneg (m + 1 : ℤ)]
              omega
            have eq7 : (m + 1) * (m ^ 3 - m) ≥ (m + 1) * (m^2 + 2 * m) := by
              apply Nat.mul_le_mul_left
              omega
            have eq8 : (m + 1) * (m^2 + 2 * m) = ((m + 1) ^ 3 - (m + 1) : ℕ) := by
              cases m with
              | zero => linarith
              | succ m =>
                cases m with
                | zero => linarith
                | succ m => 
                  simp [Nat.pow_succ, Nat.mul_assoc]
                  <;> ring_nf <;> omega
            have eq9 : (m + 1) * (m ^ 3 - m) ≥ ((m + 1) ^ 3 - (m + 1) : ℕ) := by
              linarith [eq7, eq8]
            linarith [eq9]
          linarith [eq2, eq3]
        exact Nat.le_induction base7 step k hk
      have h4 : Nat.factorial n > (n ^ 3 - n: ℕ) := by
        specialize h3 n (by linarith)
        omega
      omega
  · -- Backward implication: if n = 5 then n^3 -n = n!
    intro h_eq
    rw [h_eq]
    all_goals
      native_decide