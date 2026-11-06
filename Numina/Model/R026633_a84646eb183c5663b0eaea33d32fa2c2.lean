import Mathlib

theorem number_theory_114161 (n : ℕ) :
    (∃ k, 2^n = 6 * k + 8) ↔ Odd n ∧ n > 1 := by
  constructor
  · -- First direction: if ∃ k, 2^n = 6 * k + 8 then Odd n ∧ n > 1
    intro h
    rcases h with ⟨k, hk⟩ 
    have h1 : n > 1 := by
      by_contra h'
      push_neg at h'
      have h2 : n = 0 ∨ n = 1 := by
        omega 
      rcases h2 with (h2 | h2)
      · -- n = 0 
        rw [h2] at hk 
        omega 
      · -- n = 1 
        rw [h2] at hk 
        omega 
    have h2 : n % 2 = 1 := by
      by_contra h'
      push_neg at h'
      have h4 : n % 2 = 0 := by 
        omega 
      have h5 : n ≥ 2 := by 
        omega 
      have h6 : (2 : ℕ) ^ n % 6 = 4 := by 
        have h7 : ∀ (m : ℕ), (2 : ℕ) ^ (2 * m + 2) % 6 = 4 := by 
          intro m 
          induction m with 
          | zero => 
            norm_num 
          | succ m ih => 
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
            all_goals omega 
        have h8 : ∃ m : ℕ, n = 2 * m + 2 := by 
          refine' ⟨n / 2 - 1, by
            omega 
          ⟩ 
        rcases h8 with ⟨m, hm⟩ 
        rw [hm] 
        apply h7 m 
      have h7 : (2 : ℕ) ^ n % 6 = 2 := by 
        have h5 : (2 : ℕ) ^ n = 6 * k + 8 := by 
          omega 
        omega 
      omega 
    have h9 : Odd n := by 
      exact ⟨n / 2, by 
        omega 
      ⟩ 
    constructor 
    · exact h9 
    · exact h1 
  · -- Backward direction: If Odd n ∧ n > 1, then ∃ k, 2^n = 6 * k + 8
    rintro ⟨h_odd, h_gt⟩ 
    have h_n : n ≥ 3 := by 
      rcases h_odd with ⟨m, hm⟩ 
      omega 
    have h1 : n % 2 = 1 := by 
      rcases h_odd with ⟨m, hm⟩ 
      omega 
    have h4 : (2 : ℕ) ^ n % 6 = 2 := by 
      rcases h_odd with ⟨m, hm⟩ 
      rw [show n = 2 * m + 1 by omega] 
      have h5 : ∀ (m : ℕ), (2 : ℕ) ^ (2 * m + 1) % 6 = 2 := by 
        intro m 
        induction m with 
        | zero => 
          norm_num 
        | succ m ih => 
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
          all_goals omega 
      apply h5 m 
    have h6 : ∃ k, 2^n = 6 * k + 8 := by 
      have h8 : (6 : ℕ) ∣ ((2 : ℕ) ^ n - 8) := by 
        have h7 : (2 ^ n) % 6 = 2 := h4 
        have h9 : (2 ^ n - 8) % 6 = 0 := by 
          omega 
        exact Nat.dvd_of_mod_eq_zero h9 
      rcases h8 with ⟨k, hk⟩ 
      have h9 : n ≥ 3 := h_n 
      have h2n : (2 : ℕ) ^ n ≥ 8 := by 
        have h3 : n ≥ 3 := h9 
        have h4 : (2 : ℕ) ^ n ≥ (2 : ℕ) ^ 3 := by 
          apply Nat.pow_le_pow_of_le_right 
          all_goals 
            omega 
        have h5 : (2 : ℕ) ^ 3 = 8 := by norm_num 
        linarith 
      have h7 : 2 ^ n = 6 * k + 8 := by 
        omega 
      exact ⟨k, h7⟩ 
    exact h6