import Mathlib

theorem number_theory_295778 (n : ℕ) :
    ∃ x : ℤ, 499 * (1997 ^ n + 1) = x ^ 2 + x ↔ n = 1 := by
  by_cases h : n = 1
  · -- If n = 1, let x = 998, then 499 * (1997 ^ 1 + 1) = 998 ^ 2 + 998.
    use 998
    rw [h]
    norm_num
  · -- If n ≠ 1, we need to show that 499 * (1997 ^ n + 1) = x ^ 2 + x has no integer solutions.
    use 0
    constructor
    · -- Assume 499 * (1997 ^ n + 1) = 0^2 + 0, prove n = 1.
      intro h_eq
      have h_eq0 : 499 * (1997 ^ n + 1 : ℤ) = (0 : ℤ) := by
        nlinarith
      have h0 : (1997 : ℤ) ^ n ≥ 1 := by
        have h3 : (1997 : ℤ) ^ n ≥ 1 := by
          have h4 : 1997 ^ n ≥ 1 := by
            apply Nat.one_le_pow
            all_goals 
              omega
          exact_mod_cast h4
        linarith
      have h11 : (1997 ^ n + 1 : ℤ) ≥ 2 := by
        nlinarith
      have h12 : 499 * (1997 ^ n + 1 : ℤ) ≥ 998 := by
        nlinarith
      nlinarith
    · -- Assume n = 1, prove 499 * (1997 ^ n + 1) = 0^2 + 0.
      intro h_eq1
      exfalso
      apply h
      all_goals omega