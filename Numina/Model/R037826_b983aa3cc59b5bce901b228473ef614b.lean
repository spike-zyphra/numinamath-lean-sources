import Mathlib

theorem number_theory_206451 (n : ℕ) (h : n > 0) (g : ℕ) (hg : g ≠ 0)
    (h1 : (g / 2 + 1) * 2 ^ n = g) :
    g = 2 ^ n - 1 := by 
  have h2 : n > 0 := h
  have h3 : n ≥ 1 := by omega
  have h4 : (g / 2 + 1) * 2 ^ n > g := by
    have h5 : 2 ^ n ≥ 2 := by
      have h1 : n ≥ 1 := h3
      have h2 : 2 ^ n ≥ 2 ^ 1 := by
        apply pow_le_pow_right
        all_goals linarith
      have h3 : 2 ^ 1 = 2 := by norm_num
      linarith [h2, h3]
    by_cases h6 : g ≤ 1
    · -- Case g = 1
      have h7 : g = 1 := by
        interval_cases g <;> try { tauto }
      rw [h7] at h1
      omega
    · -- Case g > 1
      have h6 : g > 1 := by
        omega
      by_cases h8 : g % 2 = 0
      · -- Case g is even
        have h8 : g % 2 = 0 := h8
        have h9 : g ≥ 2 := by
          omega
        have h8' : (g / 2) * 2 = g := by
          omega
        nlinarith [h1, h8', h5, h6, h2]
      · -- Case g is odd
        have h7 : g % 2 = 1 := by
          omega
        have h8 : g ≥ 2 := by
          omega
        have h9 : (g / 2 + 1) * 2 ^ n % 2 = 0 := by
          have h10 : 2 ^ n % 2 = 0 := by
            have : n ≥ 1 := by omega
            have h2 : n ≥ 1 := by omega
            have h3 : 2 ^ n % 2 = 0 := by
              induction n with
              | zero =>
                omega
              | succ n ih =>
                cases n with
                | zero =>
                  simp [Nat.pow_add, Nat.mul_mod, ih]
                | succ n =>
                  simp [Nat.pow_add, Nat.mul_mod, ih]
                  all_goals omega
            omega
          have h11 : (g / 2 + 1) * 2 ^ n % 2 = 0 := by
            simp [Nat.mul_mod, h10]
          omega
        have h10 : g % 2 = 0 := by
          omega
        omega
  omega