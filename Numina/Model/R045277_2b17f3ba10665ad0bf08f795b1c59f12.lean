import Mathlib


theorem number_theory_275320 (n : ℕ) (h : ∃ m, n = m^3) :
    ∃ a b, n = a^2 - b^2 := by
  rcases h with ⟨m, hm⟩
  have h1 : (m * (m + 1)) % 2 = 0 := by
    have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h2 with (h2 | h2)
    · -- If m is even, then m * (m + 1) is even
      have : (m * (m + 1)) % 2 = 0 := by
        simp [Nat.mul_mod, Nat.add_mod, h2]
      assumption
    · -- If m is odd, then m + 1 is even, so m * (m + 1) is even
      have : (m * (m + 1)) % 2 = 0 := by
        simp [Nat.mul_mod, Nat.add_mod, h2]
      assumption

  have h3 : (m * (m - 1)) % 2 = 0 := by
    by_cases h4 : m > 0
    · 
      have h5 : m ≥ 1 := by omega
      have h6 : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases h6 with (h6 | h6)
      · -- If m is even
        have : (m * (m - 1)) % 2 = 0 := by
          have h7 : m % 2 = 0 := h6
          have h8 : (m - 1) % 2 = 1 := by
            omega
          simp [Nat.mul_mod, h7, h8]
        assumption
      · -- If m is odd
        have : (m * (m - 1)) % 2 = 0 := by
          have h7 : m % 2 = 1 := h6
          have h8 : (m - 1) % 2 = 0 := by
            omega
          simp [Nat.mul_mod, h7, h8]
        assumption
    · -- m ≤ 0, so m = 0
      have h40 : m = 0 := by omega
      rw [h40]
      all_goals norm_num

  have h14 : ∃ a, a = (m * (m + 1)) / 2 := by
    refine' ⟨(m * (m + 1)) / 2, rfl⟩

  have h15 : ∃ b, b = (m * (m - 1)) / 2 := by
    refine' ⟨(m * (m - 1)) / 2, rfl⟩

  rcases h14 with ⟨a, ha⟩
  rcases h15 with ⟨b, hb⟩

  use a, b

  have h16 : 2 * a = m * (m + 1) := by
    omega

  have h17 : 2 * b = m * (m - 1) := by
    omega

  have h18 : a ^ 2 = b ^ 2 + m ^ 3 := by
    have h19 : (2 * a) ^ 2 = (2 * b) ^ 2 + 4 * (m ^ 3 : ℕ) := by
      have h21 : (2 * a) ^ 2 = (m * (m + 1)) ^ 2 := by
        have h22 : 2 * a = m * (m + 1) := h16
        rw [h22]
      have h23 : (2 * b) ^ 2 = (m * (m - 1)) ^ 2 := by
        have h24 : 2 * b = m * (m - 1) := h17
        rw [h24]
      have h25 : (m * (m + 1)) ^ 2 = (m * (m - 1)) ^ 2 + 4 * (m ^ 3 : ℕ) := by
        cases m with
        | zero =>
          all_goals norm_num
        | succ m =>
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, mul_assoc]
          ring_nf
          <;> omega
      rw [h21, h23]
      omega
    have h27 : 4 * (a ^ 2 : ℕ) = 4 * (b ^ 2 + m ^ 3 : ℕ) := by
      have h28 : (2 * a) ^ 2 = 4 * (a ^ 2 : ℕ) := by
        ring_nf
      have h29 : (2 * b) ^ 2 = 4 * (b ^ 2 : ℕ) := by
        ring_nf
      rw [h28, h29] at h19
      omega
    omega

  have h180 : a ^ 2 ≥ b ^ 2 := by
    nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), h18]

  have h181 : n = a ^ 2 - b ^ 2 := by
    have h182 : a ^ 2 = b ^ 2 + m ^ 3 := h18
    have h183 : a ^ 2 = b ^ 2 + n := by
      rw [hm] at *
      linarith
    omega

  exact h181