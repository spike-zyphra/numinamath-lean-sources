import Mathlib

theorem algebra_108556 (a : ℕ → ℕ) (ha1 : a 1 = 3)
    (han : ∀ n, a (n + 1) = (a n - 1) ^ 2 + 1) (n : ℕ) :
    ∏ k in Finset.Icc 1 n, a k < 2 ^ (2 ^ n)
  := by 
  have h1 := han 0
  have h2 : a 1 = (a 0 - 1) ^ 2 + 1 := h1
  rw [ha1] at h2
  by_cases h3 : a 0 ≤ 1
  · -- Assume a 0 ≤ 1
    have h4 : a 0 = 0 ∨ a 0 = 1 := by
      omega
    rcases h4 with (h4 | h4)
    · -- Assume a 0 = 0
      simp [h4] at h2
      all_goals omega
    · -- Assume a 0 = 1
      simp [h4] at h2
      all_goals omega
  · -- Assume a 0 > 1
    have h5 : a 0 - 1 ≥ 1 := by
      omega
    -- From the fact that: (a0 -1) ^2 = 2, reach contradiction to Nat
    -- From h2: (a 0 - 1) ^ 2 = 2
    have h6 : (a 0 - 1 : ℕ) ^ 2 = 2 := by
      omega
    -- The right side is Nat
    have h7 : (a 0 - 1 : ℕ) ^ 2 ≥ 1 := by
      nlinarith
    -- So contradiction with right side
    -- However since 2 can't be written as square in Nat
    -- Proof becomes trivial
    have h8 : (a 0 - 1 : ℕ) ≤ 1 := by
      nlinarith [h6]
    nlinarith [h8, h6, h5]