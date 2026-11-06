import Mathlib

theorem number_theory_7727 : IsGreatest {k : ℕ | ∃ n : ℕ, 0 < n ∧ 2^k ∣ 3^n + 1} 2 := by
  constructor
  · -- Show 2 is in the set
    use 1
    all_goals norm_num
  · -- Show no value greater than 2 is in the set
    intro k hk
    rcases hk with ⟨n, hn_pos, hdiv⟩
    by_contra h
    push_neg at h
    have h3 : k ≥ 3 := by omega
    have h2 : 2 ^ 3 ∣ 2 ^ k := by
      apply pow_dvd_pow _ (by omega)
    have h3n : (2 ^ 3 : ℕ) ∣ 3 ^ n + 1 := by
      exact dvd_trans h2 hdiv
    have h4 : (3 ^ n + 1 : ℕ) % 8 = 0 := by
      omega
    have h5 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h5 with (h5 | h5)
    · -- n is even
      have h6 : (3 ^ n : ℕ) % 8 = 1 := by
        have h7 : ∀ m : ℕ, (3 ^ (2 * m) : ℕ) % 8 = 1 := by
          intro m
          induction m with
          | zero =>
            norm_num
          | succ m ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            all_goals omega
        have h8 : ∃ m : ℕ, n = 2 * m := by
          refine ⟨n / 2, by omega⟩
        rcases h8 with ⟨m, hm⟩
        rw [hm]
        exact h7 m
      omega
    · -- n is odd
      have h8 : (3 ^ n : ℕ) % 8 = 3 := by
        have h9 : ∀ m : ℕ, (3 ^ (2 * m + 1) : ℕ) % 8 = 3 := by
          intro m
          induction m with
          | zero =>
            norm_num
          | succ m ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            all_goals omega
        have h10 : ∃ m : ℕ, n = 2 * m + 1 := by
          refine ⟨(n - 1) / 2, by omega⟩
        rcases h10 with ⟨m, hm⟩
        rw [hm]
        exact h9 m
      omega