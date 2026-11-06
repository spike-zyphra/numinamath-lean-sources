import Mathlib

theorem number_theory_13655 (s : Finset ℕ) (hs : s = {x : ℕ | ∃ y : ℕ, 0 < x ∧ 0 < y ∧ x^2 - 2^y = 2021}) :
    s.sum id = 45 := by 
  have h1 : s = {45} := by 
    have h3_eq : (s : Set ℕ) = {x : ℕ | ∃ y : ℕ, 0 < x ∧ 0 < y ∧ x^2 - 2^y = 2021} := by 
      rw [hs]
      <;> aesop
    have h11 : ∀ x : ℕ, x ∈ (s : Set ℕ) ↔ x = 45 := by 
      intro x
      constructor 
      · -- Assume x ∈ s, prove x = 45 
        intro h3 
        have hx1 : x ∈ (s : Set ℕ) := h3 
        rw [h3_eq] at hx1 
        have eq1 : ∃ y : ℕ, 0 < x ∧ 0 < y ∧ x^2 - 2^y = 2021 := by 
          simpa using hx1 
        rcases eq1 with ⟨y, hx_pos, hy_pos, heq⟩ 
        by_cases h' : y < 3 
        · -- Assume y < 3. Then y = 1 or y = 2 (as y > 0)
          have h6 : y = 1 ∨ y = 2 := by 
            have : y < 3 := h'
            have hy7 : 0 < y := hy_pos 
            omega 
          rcases h6 with (r1 | r2)
          · -- Assume y = 1
            rw [show y = 1 by omega] at heq 
            have eq1' : x^2 = 2023 := by 
              omega 
            have eq1_mod : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by 
              have h11 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by 
                omega 
              rcases h11 with (h11 | h11 | h11 | h11) <;> simp [Nat.pow_mod, h11]
            have eq2_mod : x^2 % 4 = 3 := by 
              omega 
            omega 
          · -- Assume y = 2 
            rw [show y = 2 by omega] at heq 
            have eq1' : x^2 = 2025 := by 
              omega 
            have : x = 45 := by 
              have h5' : x^2 = 2025 := eq1' 
              have h61 : x ≤ 45 := by nlinarith 
              interval_cases x <;> omega 
            assumption 
        · -- Assume y ≥ 3 
          have h7 : y ≥ 3 := by omega 
          -- Show contradiction using modulo 8 
          have h5 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by 
            have h11 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
              omega 
            rcases h11 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod]
          -- Show that 2^y % 8 = 0 
          have h3 : (2 ^ y) % 8 = 0 := by 
            have h27 : y ≥ 3 := h7 
            have h77 : ∀ (k : ℕ), (2 ^ (k + 3)) % 8 = 0 := by 
              intro k 
              induction k with 
              | zero =>
                norm_num 
              | succ k ih =>
                simp [Nat.pow_add, Nat.mul_mod] at ih ⊢ 
                all_goals omega 
            specialize h77 (y - 3)
            have h78 : (y - 3) + 3 = y := by omega 
            rw [h78] at h77 
            assumption 
          -- Show that x^2 % 8 = 5 
          have eq3_eq : x^2 = 2^y + 2021 := by 
            omega 
          have eq3_mod : x^2 % 8 = 5 := by 
            omega 
          omega 
      · -- Assume x = 45, prove x in s 
        intro h 
        rw [h] 
        rw [h3_eq] 
        use 2 
        all_goals norm_num 
    have h2 : s = {45} := by 
      ext x 
      simp only [Finset.mem_singleton]
      have h22 : x ∈ (s : Set ℕ) ↔ x = 45 := h11 x 
      simp at h22 ⊢ 
      all_goals tauto 
    exact h2 
  rw [h1]
  simp