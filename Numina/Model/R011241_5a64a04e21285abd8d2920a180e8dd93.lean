import Mathlib

-- we show a simple lemma which will be used in the proof
lemma lemma_1 (m n: ℕ) (h1: 0 < n) (h2: n < m) (h3: Nat.Prime (m * n)): n = 1 := by
    rw [Nat.prime_mul_iff] at h3
    rcases h3 with h | h
    .
      omega
    .
      have o: n = 0 := by omega
      simp [o] at h
      norm_num at h

theorem number_theory_231716: (¬ ∃ m n: ℕ, 0 < n ∧ n < m ∧ Nat.Prime (m + n) ∧ Nat.Prime (m - n) ∧
Nat.Prime (m * n) ∧ Nat.Prime (m / n)) ∧
  ∃ m n: ℕ, 0 < n ∧ n < m ∧ Nat.Prime (m + n) ∧ Nat.Prime (m * n) ∧ Nat.Prime (m / n) := by
  constructor
  · -- Assume that there exist such m and n that satisfy all 4 expressions being prime, derives a contradiction
    intro h
    rcases h with ⟨m, n, hn, h1, hp1, hp2, hp3, hp4⟩
    have h4: n = 1 := lemma_1 m n hn h1 hp3
    have h5: Nat.Prime (m + 1) := by
      have h7 : n = 1 := h4
      rw [h7] at hp1
      norm_num at hp1 ⊢
      exact hp1
    have h6: m > 1 := by
      omega
    have h8: Nat.Prime m := by
      have h9: n = 1 := h4
      rw [h9] at hp3
      simp at hp3 ⊢
      exact hp3
    have h9: Nat.Prime (m - 1) := by
      have h7 : n = 1 := h4
      rw [h7] at hp2
      norm_num at hp2 ⊢
      exact hp2
    by_cases h : m > 3
    · -- Assume m > 3, prove contradiction
      have h11: m % 2 = 1 := by
        by_contra h'
        have h' : m % 2 = 0 := by
          omega
        have h12: ¬ Nat.Prime m := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ m by omega) (by omega) (by omega)
        tauto
      have h12: m % 3 = 1 ∨ m % 3 = 2 := by
        by_contra h
        push_neg at h
        have h13: m % 3 = 0 := by
          omega
        have  h14: ¬ Nat.Prime m := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ m by omega) (by omega) (by omega)
        tauto
      rcases h12 with (h12 | h12)
      · -- Assume m % 3 = 1
        have h13: (m - 1) % 3 = 0 := by
          omega
        have h14: ¬ Nat.Prime (m - 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (m - 1) by omega) (by omega) (by omega)
        tauto
      · -- Assume m % 3 = 2
        have h14: (m + 1) % 3 = 0 := by
          omega
        have h15: ¬  Nat.Prime (m + 1) := by
          apply  Nat.not_prime_of_dvd_of_lt (show 3 ∣ (m + 1) by omega) (by omega) (by omega)
        tauto
    · -- Assume m ≤ 3
      have h16: m = 2 ∨ m = 3 := by
        interval_cases m <;> omega
      rcases h16 with (h16 | h16)
      · -- Assume m = 2
        have h5' : m = 2 := h16
        rw [h5'] at h9
        norm_num at h9
      · -- Assume m = 3
        have h5' : m = 3 := h16
        rw [h5'] at h5
        norm_num at h5
  · -- Second part: there exist m and n such that 3 expressions are prime
    use 2, 1
    constructor
    · -- 0 < n
      norm_num
    constructor
    · -- n < m
      norm_num
    constructor
    · -- Nat.Prime (m + n)
      norm_num
    constructor
    · -- Nat.Prime (m * n)
      norm_num
    · -- Nat.Prime (m / n)
      norm_num