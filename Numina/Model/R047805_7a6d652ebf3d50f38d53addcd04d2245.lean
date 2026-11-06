import Mathlib

theorem number_theory_33091 : IsGreatest {k | ∀ n > 0, 2 ^ k ∣ 3 ^ (2 * n + 3) + 40 * n - 27} 6 := by
  constructor
  · -- Show 6 is in the set
    intro n hn
    have h1 : ∀ n > 0, 2 ^ 6 ∣ 3 ^ (2 * n + 3) + 40 * n - 27 := by
      intro n hn
      have h2 : ∀ n : ℕ, n > 0 → 2 ^ 6 ∣ 3 ^ (2 * n + 3) + 40 * n - 27 := by
        intro n hn
        induction n with
        | zero =>
          linarith
        | succ n ih =>
          cases n with
          | zero =>
            norm_num at *
          | succ n =>
            simp [pow_succ, pow_mul] at ih ⊢
            ring_nf at ih ⊢
            all_goals
              omega
      exact h2 n hn
    specialize h1 n hn
    simpa using h1
  · -- Show 6 is greatest
    intro k hk
    have h2 : ∀ n > 0, 2 ^ k ∣ 3 ^ (2 * n + 3) + 40 * n - 27 := by
      simpa using hk
    have h3 := h2 2 (by norm_num)
    norm_num at h3
    by_contra h
    push_neg at h
    have h4 : k ≥ 7 := by
      omega
    have h5 : ¬ (2 ^ 7 ∣ 2240) := by
      norm_num
    have h6 : 2 ^ 7 ∣ 2240 := by
      have h7 : 2 ^ k ∣ 2240 := by
        simpa using h3
      have h8 : k ≥ 7 := by
        omega
      have h9 : 2 ^ 7 ∣ 2 ^ k := by
        apply pow_dvd_pow _ (by omega)
      have h10 : 2 ^ k ∣ 2240 := h7
      have h11 : 2 ^ 7 ∣ 2240 := by
        apply dvd_trans h9 h7
      exact h11
    contradiction