import Mathlib

theorem number_theory_161284 (n : ℕ) :
    Nat.factorial n + 1 = (10 * n + 1) ^ 2 ↔ n = 7 := by
  constructor
  · -- Assume Nat.factorial n + 1 = (10 * n + 1) ^ 2, prove n = 7
    intro h
    by_cases h1 : n ≤ 7
    · -- n ≤ 7
      interval_cases n <;> try { simp [Nat.factorial] at h ⊢; all_goals omega }
    · -- n > 7
      have h2 : n ≥ 8 := by
        omega
      have h3 : Nat.factorial n > (10 * n + 1) ^ 2 := by
        have h4 : ∀ (k : ℕ), k ≥ 8 → Nat.factorial k > (10 * k + 1) ^ 2 := by
          intro k hk
          have base := show Nat.factorial 8 > (10 * 8 + 1) ^ 2 by
            norm_num [Nat.factorial]
          have step : ∀ (k : ℕ), k ≥ 8 → Nat.factorial k > (10 * k + 1) ^ 2 →
              Nat.factorial (k + 1) > (10 * (k + 1) + 1) ^ 2 := by
            intros k hk h
            have h5 : Nat.factorial (k + 1) = (k + 1) * (Nat.factorial k) := by
              simp [Nat.factorial]
              <;> ring
            rw [h5]
            nlinarith [h, sq_nonneg ((k : ℕ) : ℕ), sq_nonneg ((10 * k + 1) : ℕ), sq_nonneg ((10 * (k + 1) + 1) : ℕ), mul_pos (show 0 < (1 : ℕ) by norm_num) (show 0 < (1 : ℕ) by norm_num), sq_nonneg ((k : ℕ) - 7 : ℤ)]
          exact Nat.le_induction base step k hk
        specialize h4 n h2
        simpa using h4
      nlinarith [h, h3]
  · -- Assume n = 7, prove Nat.factorial n + 1 = (10 * n + 1) ^ 2
    intro h
    rw [h]
    all_goals norm_num [Nat.factorial]