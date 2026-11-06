import Mathlib

theorem number_theory_165357 (n : ℕ) (h : ¬ 10 ∣ ∑ i ∈ Finset.Icc 1981 1984, i^n) :
    ∃ k, n = 4 * k := by
  have h1 : (1981 ^ n + 1982 ^ n + 1983 ^ n + 1984 ^ n : ℕ) % 10 ≠ 0 := by
    have h2 : ¬ 10 ∣ ∑ i ∈ Finset.Icc 1981 1984, i^n := h
    norm_num [Finset.sum_Icc_succ_top] at h2 ⊢
    omega

  have h2 : n % 4 = 0 := by
    by_contra h2
    push_neg at h2
    have h3 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    have h4 : (1981 ^ n + 1982 ^ n + 1983 ^ n + 1984 ^ n : ℕ) % 10 = 0 := by
      have h5 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := h3
      rcases h5 with (h5 | h5 | h5)
      · -- case where n % 4 = 1
        have h6 : n = 4 * (n / 4) + 1 := by
          omega
        rw [h6]
        have h7 : ∀ k : ℕ, (1981 ^ (4 * k + 1) + 1982 ^ (4 * k + 1) + 1983 ^ (4 * k + 1) + 1984 ^ (4 * k + 1) : ℕ) % 10 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            ring_nf at ih ⊢
            all_goals
              omega
        specialize h7 (n / 4)
        simpa using h7
      · -- case where n % 4 = 2
        have h6 : n = 4 * (n / 4) + 2 := by
          omega
        rw [h6]
        have h7 : ∀ k : ℕ, (1981 ^ (4 * k + 2) + 1982 ^ (4 * k + 2) + 1983 ^ (4 * k + 2) + 1984 ^ (4 * k + 2) : ℕ) % 10 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            ring_nf at ih ⊢
            all_goals
              omega
        specialize h7 (n / 4)
        simpa using h7
      · -- case where n % 4 = 3
        have h6 : n = 4 * (n / 4) + 3 := by
          omega
        rw [h6]
        have h7 : ∀ k : ℕ, (1981 ^ (4 * k + 3) + 1982 ^ (4 * k + 3) + 1983 ^ (4 * k + 3) + 1984 ^ (4 * k + 3) : ℕ) % 10 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            ring_nf at ih ⊢
            all_goals
              omega
        specialize h7 (n / 4)
        simpa using h7
    omega

  have h3 : ∃ k, n = 4 * k := by
    have : n % 4 = 0 := h2
    refine' ⟨n / 4, by omega⟩
  exact h3