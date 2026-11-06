import Mathlib

theorem number_theory_157635 (x y : ℕ) : 5^x - 2^y = 3 ↔ (x, y) = (1, 1) := by
  constructor
  · -- Assume 5^x - 2^y = 3, prove (x, y) = (1, 1)
    intro h
    have h1 : 5 ^ x = 2 ^ y + 3 := by
      omega
    by_cases hx : x > 1
    · -- x > 1
      have hx2 : x ≥ 2 := by omega
      have h2 : (5 ^ x : ℕ) % 4 = 1 := by
        have h3 : ∀ (n : ℕ), (5 ^ n : ℕ) % 4 = 1 := by
          intro n
          induction n with
          | zero =>
            norm_num
          | succ n ih =>
            simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
            all_goals omega
        specialize h3 x
        simpa using h3
      have h3 : (2 ^ y : ℕ) % 4 = 2 := by
        omega
      have h4 : y ≤ 1 := by
        by_contra h5
        push_neg at h5
        have h5' : y ≥ 2 := by omega
        have h7 : (2 ^ y : ℕ) % 4 = 0 := by
          have h8 : (2 ^ y : ℕ) % 4 = 0 := by
            have h9 : ∀ (k : ℕ), (2 ^ (k + 2) : ℕ) % 4 = 0 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                have eq1 : 2 ^ (k + 1 + 2) = 2 ^ (k + 2) * 2 := by ring_nf
                rw [eq1]
                simp [Nat.mul_mod, ih]
                <;> omega
            have h10 : y ≥ 2 := by linarith
            have eq3 : y - 2 + 2 = y := by
              omega
            specialize h9 (y - 2)
            simp [eq3] at h9 ⊢
            all_goals omega
          exact h8
        omega
      have h4 : y = 0 ∨ y = 1 := by
        omega
      rcases h4 with (h4 | h4)
      · -- y = 0
        have h5 : y = 0 := h4
        rw [h5] at h1
        have h11 : 5 ^ x = 4 := by
          omega
        have h6 : x ≤ 1 := by
          by_contra h6
          push_neg at h6
          have h7 : 5 ^ x ≥ 25 := by
            have h8 : x ≥ 2 := by omega
            have h9 : 5 ^ x ≥ 5 ^ 2 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals linarith
            have h10 : 5 ^ 2 = 25 := by norm_num
            have h11 : 5 ^ x ≥ 25 := by
              omega
            linarith
          linarith
        interval_cases x <;> omega
      · -- y = 1
        have h5 : y = 1 := h4
        rw [h5] at h1
        have h10 : 5 ^ x = 5 := by
          omega
        have h11 : x = 1 := by
          have h12 : 5 ^ x = 5 ^ 1 := by
            rw [h10]
            all_goals norm_num
          have h13 : x = 1 := by
            exact Nat.pow_right_injective (by norm_num) h12
          exact h13
        omega
    · -- x ≤ 1
      have hx3 : x ≤ 1 := by omega
      have h2 : x = 0 ∨ x = 1 := by
        interval_cases x <;> omega
      rcases h2 with (h | h)
      · -- x = 0
        have h4 : x = 0 := h
        rw [h4] at h1
        have h5 : 2 ^ y + 3 = 1 := by
          omega
        have h6 : 2 ^ y ≥ 1 := by
          have h9 : y ≥ 0 := by omega
          have h10 : 2 ^ y ≥ 2 ^ 0 := by
            apply Nat.pow_le_pow_of_le_right
            all_goals norm_num
          have h11 : 2 ^ 0 = 1 := by norm_num
          have h12 : 2 ^ y ≥ 1 := by
            linarith [h11, h10]
          linarith
        omega
      · -- x = 1
        have h8 : x = 1 := h
        rw [h8] at h1
        have h10 : 2 ^ y = 2 := by
          omega
        have h11 : y = 1 := by
          have h12 : 2 ^ y = 2 ^ 1 := by
            rw [h10]
            all_goals norm_num
          exact Nat.pow_right_injective (by norm_num) h12
        simp [h8, h11]
  · -- Assume (x, y) = (1, 1), prove 5^x - 2^y = 3
    rintro ⟨rfl, rfl⟩
    norm_num