import Mathlib

theorem number_theory_269979 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a^3 - b^3 - c^3 = 3 * a * b * c) (h2 : a^2 = 2 * (b + c)) :
    a = 2 ∧ b = 1 ∧ c = 1 := by
  have eq1 : a ^ 3 = b ^ 3 + c ^ 3 + 3 * a * b * c := by
    have h3 : a ^ 3 ≥ b ^ 3 + c ^ 3 := by
      by_contra h
      push_neg at h
      have h4 : a ^ 3 < b ^ 3 + c ^ 3 := by
        omega
      have h10 : a ^ 3 - b ^ 3 - c ^ 3 = 0 := by
        have h11 : a ^ 3 ≤ b ^ 3 + c ^ 3 := by
          omega
        omega
      have h11 : 3 * a * b * c = 0 := by
        omega
      have h11 : 3 * a * b * c > 0 := by
        have h3a : a > 0 := ha
        have h3b : b > 0 := hb
        have h3c : c > 0 := hc
        have h10 : a ≥ 1 := by omega
        have h11 : b ≥ 1 := by omega
        have h12 : c ≥ 1 := by omega
        have h20 : 3 * a * b * c ≥ 3 * 1 * 1 * 1 := by
          have h3a1 : a ≥ 1 := h10
          have h3b1 : b ≥ 1 := h11
          have h3c1 : c ≥ 1 := h12
          have h30 : a * b * c ≥ 1 * 1 * 1 := by
            apply Nat.mul_le_mul
            apply Nat.mul_le_mul
            all_goals
              omega
          nlinarith
        nlinarith
      omega
    omega
  have h3 : a % 2 = 0 := by
    have h4 : a ^ 2 % 2 = 0 := by
      have h5 : a ^ 2 = 2 * (b + c) := by
        omega
      omega
    by_contra h
    push_neg at h
    have h5 : a % 2 = 1 := by
      omega
    have h6 : a ^ 2 % 2 = 1 := by
      simp [Nat.pow_mod, h5]
    omega
  have h4 : ∃ k : ℕ, a = 2 * k := by
    refine' ⟨a / 2, by omega⟩
  rcases h4 with ⟨k, hk⟩
  have h5 : b + c = 2 * k ^ 2 := by
    have h6 : a ^ 2 = 2 * (b + c) := h2
    rw [hk] at h6
    nlinarith
  have h14 : (2 * k) ^ 3 = b ^ 3 + c ^ 3 + 3 * (2 * k) * b * c := by
    have h8 : a ^ 3 = b ^ 3 + c ^ 3 + 3 * a * b * c := eq1
    rw [hk] at h8
    linarith
  have h5a : k = 1 := by
    by_cases h6 : k > 1
    ·
      have h7 : k ≥ 2 := by omega
      have h8 : b + c ≥ 8 := by nlinarith [h5, h7]
      nlinarith [sq_nonneg (b - c : ℤ), sq_nonneg ((b + c : ℤ) - 2), sq_nonneg ((k : ℤ) - 1), sq_nonneg (b + c : ℤ), sq_nonneg (b - 1 : ℤ), sq_nonneg (c - 1 : ℤ)]
    ·
      have h7 : k ≤ 1 := by omega
      have h8 : k = 1 := by
        by_cases h9 : k < 1
        ·
          have h10 : k = 0 := by omega
          rw [h10] at hk
          have h11 : a = 0 := by linarith
          omega
        ·
          omega
      exact h8
  have h38 : a = 2 := by
    nlinarith [hk, h5a]
  have h39 : b + c = 2 := by
    nlinarith [h5, h5a]
  have h40 : b = 1 := by
    have h40 : b ≤ 1 := by
      omega
    have h41 : b ≥ 1 := by
      omega
    omega
  have h42 : c = 1 := by
    omega
  exact ⟨by linarith, by linarith, by linarith⟩