import Mathlib

theorem number_theory_98984 (n : ℕ) :
    ∃ k, k^2 = 2^8 + 2^11 + 2^n ↔ n = 12 := by
  by_cases h : n = 12
  · -- Assume n = 12, prove ∃ k, k^2 = 2^8 + 2^11 + 2^n ↔ n = 12
    use 80
    rw [h]
    all_goals
      norm_num
  · -- Assume n ≠ 12, prove ∃ k, k^2 = 2^8 + 2^11 + 2^n ↔ n = 12
    use 0
    constructor
    · -- Assume k^2 = 2^8 + 2^11 + 2^n, prove n = 12
      intro h_eq
      have h1 : 2^8 + 2^11 + 2^n = 0 := by
        nlinarith
      have h2 : 2^8 + 2^11 + 2^n > 0 := by
        have h3 : 2^8 > 0 := by norm_num
        have h4 : 2^11 > 0 := by norm_num
        have h5 : 2^n > 0 := by positivity
        linarith
      linarith
    · -- Assume n = 12, prove k^2 = 2^8 + 2^11 + 2^n
      intro h_eq
      exfalso
      tauto