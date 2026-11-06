import Mathlib

theorem number_theory_8293 : ∀ n : ℕ, (1 < n) → ¬((2^n : ℤ) ∣ (3^n + 1)) := by
  intro n hn
  by_contra h
  have h1 : n ≥ 2 := by linarith
  have h2 : n ≥ 2 := h1
  by_cases h4 : n ≤ 3
  · -- n ≤ 3, so n = 2 or 3
    interval_cases n <;> norm_num at h ⊢
    all_goals omega
  · -- n > 3
    have h4 : n ≥ 4 := by
      omega
    have h5 : (3 ^ n + 1 : ℤ) % 8 = 4 ∨ (3 ^ n + 1 : ℤ) % 8 = 2 := by
      have h6 : ∀ k : ℕ, (3 ^ (2 * k + 1 : ℕ) + 1 : ℤ) % 8 = 4 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      have h7 : ∀ k : ℕ, (3 ^ (2 * k + 2 : ℕ) + 1 : ℤ) % 8 = 2 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      by_cases h8 : n % 2 = 1
      · 
        have h9 : ∃ k : ℕ, n = 2 * k + 1 := by
          have : n % 2 = 1 := h8
          refine' ⟨(n - 1) / 2, by omega⟩
        rcases h9 with ⟨k, hk⟩
        have hk' : n = 2 * k + 1 := by
          linarith
        rw [show (3 ^ n + 1 : ℤ) = (3 ^ (2 * k + 1) + 1 : ℤ) by rw [hk']]
        have hk1 : (3 ^ (2 * k + 1) + 1 : ℤ) % 8 = 4 := h6 k
        tauto
      · 
        have h8' : n % 2 = 0 := by 
          omega
        have h9 : ∃ k : ℕ, n = 2 * k + 2 := by
          have : n % 2 = 0 := h8'
          refine' ⟨(n / 2) - 1, by omega⟩
          all_goals omega
        rcases h9 with ⟨k, hk⟩
        have hk' : n = 2 * k + 2 := by
          linarith
        rw [show (3 ^ n + 1 : ℤ) = (3 ^ (2 * k + 2) + 1 : ℤ) by rw [hk']]
        have hk2 : (3 ^ (2 * k + 2) + 1 : ℤ) % 8 = 2 := h7 k
        tauto
    have h8 : (3 ^ n + 1 : ℤ) % 8 = 0 := by
      have h2n : (2^n : ℤ) ∣ (3^n + 1) := h
      have h3 : (8 : ℤ) ∣ (2^n : ℤ) := by
        have : n ≥ 3 := by
          omega
        have h5 : (2^n : ℤ) % 8 = 0 := by
          have h6 : ∀ k : ℕ, (2^(k + 3) : ℤ) % 8 = 0 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [pow_succ, pow_add] at ih ⊢
              all_goals omega
          specialize h6 (n - 3)
          have h7 : n - 3 + 3 = n := by
            omega
          rw [h7] at h6
          tauto
        omega
      have h3' : (8 : ℤ) ∣ (3^n + 1) := by
        exact dvd_trans h3 h2n
      exact Int.emod_eq_zero_of_dvd h3'
    omega