import Mathlib

theorem number_theory_239843 (a n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    ∃ k : ℤ, (a + 1)^n - a^n = k * n ↔ (a, n) = (a, 1) := by 
  use if n = 1 then 1 else 0
  constructor 
  · -- Assume (a + 1)^n - a^n = k * n, prove (a, n) = (a, 1)
    intro h 
    by_cases h1 : n = 1 
    · -- Case n = 1, then (a + 1)^1 - a^1 = 1, and (a, n) = (a, 1)
      simp [h1] at h 
      simp [h1]
    · -- Case n ≠ 1 
      have h2 : n > 1 := by 
        by_contra h'
        push_neg at h'
        have : n = 1 := by linarith 
        tauto 
      have h7 : (a + 1 : ℤ) ^ n - (a : ℤ) ^ n ≠ 0 := by 
        have h7a : (a + 1 : ℤ) ^ n > (a : ℤ) ^ n := by 
          have h8a : (a + 1 : ℤ) > (a : ℤ) := by 
            omega 
          have h9a : (a + 1 : ℤ) ^ n > (a : ℤ) ^ n := by 
            apply pow_lt_pow_left 
            all_goals linarith 
          linarith 
        omega 
      have h8 : (a + 1 : ℤ) ^ n - (a : ℤ) ^ n = (if n = 1 then (1 : ℤ) else (0 : ℤ)) * (n : ℤ) := by 
        exact_mod_cast h 
      have h9 : (if n = 1 then (1 : ℤ) else (0 : ℤ)) * (n : ℤ) = 0 := by 
        have h10 : n ≠ 1 := h1 
        simp [h10] 
      rw [h9] at h8 
      have h10 : (a + 1 : ℤ) ^ n - (a : ℤ) ^ n > 0 := by 
        have h7a : (a + 1 : ℤ) ^ n > (a : ℤ) ^ n := by 
          have h8a : (a + 1 : ℤ) > (a : ℤ) := by 
            omega 
          have h9a : (a + 1 : ℤ) ^ n > (a : ℤ) ^ n := by 
            apply pow_lt_pow_left 
            all_goals linarith 
          linarith 
        linarith 
      omega 
  · -- Assume (a, n) = (a, 1), prove (a + 1)^n - a^n = k * n
    intro h 
    have hn1 : n = 1 := by
      have h1 : (a, n) = (a, 1) := h
      simp [Prod.ext_iff] at h1
      omega 
    have h3 : (n : ℤ) = 1 := by exact_mod_cast hn1 
    simp [hn1] at *
    all_goals linarith