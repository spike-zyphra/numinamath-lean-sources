import Mathlib

theorem number_theory_217935 (n : ℕ) (h : n^2 ≡ 44 [MOD 100]) :
    n ≡ 12 [ZMOD 100] ∨ n ≡ 62 [ZMOD 100] ∨ n ≡ 38 [ZMOD 100] ∨ n ≡ 88 [ZMOD 100] := by
  norm_num [Nat.ModEq] at h 
  have h1 : n ^ 2 % 100 = 44 := h
  have h2 : n % 100 = 12 ∨ n % 100 = 62 ∨ n % 100 = 38 ∨ n % 100 = 88 := by
    by_cases h3 : n ≤ 99 
    · interval_cases n <;> norm_num at h1 <;> omega 
    · -- n > 99
      have h4 : n ≥ 100 := by omega 
      have h9 : (n : ℕ) % 100 = 12 ∨ (n : ℕ) % 100 = 62 ∨ (n : ℕ) % 100 = 38 ∨ (n : ℕ) % 100 = 88 := by
        have h10 : (n : ℕ) ^ 2 % 100 = 44 := h1 
        have h14 : (n ^ 2) % 100 = 44 := h1
        have h17 : (n % 100) ^ 2 % 100 = 44 := by 
          have h15 : (n ^ 2) % 100 = 44 := h1 
          have h16 : (n ^ 2) % 100 = ((n % 100) ^ 2) % 100 := by 
            simp [Nat.pow_mod]
          rw [h16] at h15 
          exact h15 
        have h18 : n % 100 < 100 := by 
          omega 
        interval_cases (n % 100) <;> norm_num at h17 <;> omega 
      omega 
  rcases h2 with (h2 | h2 | h2 | h2)
  · -- Convert to integer congruence
    norm_num [Int.ModEq] 
    omega 
  · -- Convert to integer congruence
    norm_num [Int.ModEq] 
    omega 
  · -- Convert to integer congruence
    norm_num [Int.ModEq] 
    omega 
  · -- Convert to integer congruence
    norm_num [Int.ModEq] 
    omega