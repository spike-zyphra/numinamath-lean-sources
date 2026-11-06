import Mathlib

theorem number_theory_193529 (x y : ℕ) : 2^x - 1 = 5^y ↔ x = 1 ∧ y = 0 := by
  constructor
  · -- Forward direction: if $2^x - 1 = 5^y$, then $(x, y) = (1, 0)$
    intro h
    have h1 : 2 ^ x = 5 ^ y + 1 := by
      have h2 : 2 ^ x ≥ 1 := by
        have h3 : ∀ (n : ℕ), 2 ^ n ≥ 1 := by
          intro n
          induction n with
          | zero =>
            norm_num
          | succ n ih =>
            simp [pow_succ] at ih ⊢
            all_goals linarith
        specialize h3 x
        linarith
      omega
    -- Show x ≥ 1
    have h2 : x ≥ 1 := by
      by_contra h2
      push_neg at h2
      have h3 : x = 0 := by
        omega
      rw [h3] at h1
      have h4 : 5 ^ y = 0 := by
        nlinarith
      have h5 : 5 ^ y > 0 := by
        positivity
      linarith
    -- Show x = 1
    have h3 : x = 1 := by
      by_cases h4 : x ≥ 2
      · -- x >= 2, so 2^x % 4 = 0
        have h5 : (2 : ℕ) ^ x % 4 = 0 := by
          have h6 : ∀ (n : ℕ), (2 : ℕ) ^ (n + 2) % 4 = 0 := by
            intro n
            induction n with
            | zero => norm_num
            | succ n ih =>
              simp [Nat.pow_succ, Nat.pow_add] at ih ⊢
              all_goals omega
          specialize h6 (x - 2)
          have h7 : x - 2 + 2 = x := by omega
          rw [h7] at h6
          exact h6
        have h8 : (5 ^ y + 1) % 4 = 2 := by
          have h9 : ∀ (y : ℕ), (5 ^ y : ℕ) % 4 = 1 := by
            intro y
            induction y with
            | zero => norm_num
            | succ y ih =>
              simp [Nat.pow_succ] at ih ⊢
              all_goals omega
          have h10 : (5 ^ y) % 4 = 1 := h9 y
          omega
        have h11 : (2 : ℕ) ^ x % 4 = (5 ^ y + 1) % 4 := by
          omega
        rw [h5] at h11
        omega
      · -- x < 2, and x ≥ 1 => x = 1
        have h5 : x = 1 := by
          omega
        exact h5
    -- Show y = 0
    have h4 : y = 0 := by
      have h5 : 5 ^ y = 1 := by
        have h6 : 2 ^ x = 5 ^ y + 1 := h1
        rw [h3] at h6
        nlinarith
      have h7 : y = 0 := by
        have h8 : 5 ^ y = 1 := h5
        have h9 : y = 0 := by
          have h10 : 5 ^ 0 = 1 := by norm_num
          have h11 : 5 ^ y = 1 := h8
          have h12 : y = 0 := by
            exact Nat.pow_right_injective (by norm_num) h11
          exact h12
        exact h9
      exact h7
    exact ⟨by omega, by omega⟩
  · -- Backward direction: if (x, y) = (1, 0), then 2^x - 1 = 5^y
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    all_goals norm_num