import Mathlib

theorem number_theory_292490 (n : ℕ) (hn : 1 < n) :
    ¬∃ k, k^2 = 2^n - 1 := by
  rintro ⟨k, hk⟩
  have h2 : n ≥ 2 := by linarith
  have h3 : (2 : ℕ) ^ n % 4 = 0 := by
    have h4 : ∀ (n : ℕ), n ≥ 2 → (2 : ℕ) ^ n % 4 = 0 := by
      intro n hn
      have base2 : (2 ^ 2) % 4 = 0 := by norm_num
      have step : ∀ (m : ℕ), m ≥ 2 → (2 : ℕ) ^ m % 4 = 0 → (2 : ℕ) ^ (m + 1) % 4 = 0 := by
        intros m hm h
        have : (2 : ℕ) ^ (m + 1) = (2 ^ m) * 2 := by ring
        rw [this]
        simp [Nat.mul_mod, h]
        all_goals norm_num
        all_goals omega
      exact Nat.le_induction base2 step n hn
    apply h4 n h2
  have h6 : n ≥ 2 := h2
  have h7 : (2 : ℕ) ^ n ≥ 4 := by
    have h8 : (2 : ℕ) ^ 2 = 4 := by norm_num
    have h9 : (2 : ℕ) ^ n ≥ (2 : ℕ) ^ 2 := by
      apply Nat.pow_le_pow_of_le_right
      all_goals norm_num
      all_goals linarith
    have h10 : (2 : ℕ) ^ 2 = 4 := by norm_num
    linarith [h8, h9, h10]
  have h9 : k^2 % 4 = 0 ∨ k^2 % 4 = 1 := by
    have h10 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
      omega
    rcases h10 with (h | h | h | h)
    · simp [pow_two, Nat.mul_mod, h]
    · simp [pow_two, Nat.mul_mod, h]
    · simp [pow_two, Nat.mul_mod, h]
    · simp [pow_two, Nat.mul_mod, h]
  have h10 : (2^n - 1 : ℕ) % 4 = 3 := by
    have h11 : (2^n : ℕ) % 4 = 0 := h3
    omega
  have h11 : k^2 = 2^n - 1 := by
    linarith
  have h12 : k^2 % 4 = 3 := by
    omega
  omega