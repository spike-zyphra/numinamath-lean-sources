import Mathlib

theorem number_theory_4420 (p : ℕ) (hp : Nat.Prime p) (h : 13 ≤ p) :
    ∃ n m, n + m = p ∧ n ≠ 1 ∧ ¬Nat.Prime n ∧ m ≠ 1 ∧ ¬Nat.Prime m ∧ Nat.Coprime n m := by
  have hp1 : p ≥ 13 := h
  have h2 : p % 2 = 1 := by
    by_contra h'
    push_neg at h'
    have : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    tauto
  have h6 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h99 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h99 with (h99 | h99 | h99)
    · -- p % 3 = 0
      have hp0 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
      tauto
    ·
      tauto
    ·
      tauto
  rcases h6 with (h6 | h6)
  · -- Case where p ≡ 1 (mod 3).
    use 4
    use p - 4
    constructor
    · -- Show that 4 + (p - 4) = p
      omega
    constructor
    · -- Show 4 ≠ 1
      omega
    constructor
    · -- Show that ¬Nat.Prime 4. 4 is composite.
      norm_num
    constructor
    · -- Show that p - 4 ≠ 1
      by_contra h'
      have h1 : p - 4 = 1 := by omega
      have h2 : p = 5 := by omega
      all_goals linarith
    constructor
    · -- Show that ¬Nat.Prime (p - 4)
      have hp4 : p - 4 > 1 := by
        omega
      have h8 : (p - 4) % 3 = 0 := by
        omega
      have h9 : (p - 4) > 3 := by
        omega
      have h4 : ¬Nat.Prime (p - 4) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p - 4) by omega) (by omega) (by omega)
      exact_mod_cast h4
    · -- Show that Nat.Coprime 4 (p - 4)
      have h9 : Nat.Coprime 4 (p - 4) := by
        have h10 : Nat.gcd 4 (p - 4) ∣ 4 := by
          exact Nat.gcd_dvd_left 4 (p - 4)
        have h11 : Nat.gcd 4 (p - 4) ∣ (p - 4) := by
          exact Nat.gcd_dvd_right 4 (p - 4)
        have h12 : Nat.gcd 4 (p - 4) ≤ 4 := by
          exact Nat.le_of_dvd (by norm_num) h10
        interval_cases h : Nat.gcd 4 (p - 4) <;> omega
      exact_mod_cast h9
  · -- Case where p ≡ 2 (mod 3).
    use 8
    use p - 8
    constructor
    · -- Show that 8 + (p - 8) = p
      omega
    constructor
    · -- Show 8 ≠ 1
      omega
    constructor
    · -- Show that ¬Nat.Prime 8. 8 is composite.
      norm_num
    constructor
    · -- Show that p - 8 ≠ 1
      by_contra h'
      have h1 : p - 8 = 1 := by omega
      have h2 : p = 9 := by omega
      all_goals linarith
    constructor
    · -- Show that ¬Nat.Prime (p - 8)
      have hp5 : p - 8 > 1 := by
        omega
      have h8 : (p - 8) % 3 = 0 := by
        omega
      have h9 : (p - 8) > 3 := by
        omega
      have h4 : ¬Nat.Prime (p - 8) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p - 8) by omega) (by omega) (by omega)
        all_goals omega
      exact_mod_cast h4
    · -- Show that Nat.Coprime 8 (p - 8)
      have h9 : Nat.Coprime 8 (p - 8) := by
        have h10 : Nat.gcd 8 (p - 8) ∣ 8 := by
          exact Nat.gcd_dvd_left 8 (p - 8)
        have h11 : Nat.gcd 8 (p - 8) ∣ (p - 8) := by
          exact Nat.gcd_dvd_right 8 (p - 8)
        have h12 : Nat.gcd 8 (p - 8) ≤ 8 := by
          exact Nat.le_of_dvd (by norm_num) h10
        interval_cases h : Nat.gcd 8 (p - 8) <;> omega
      exact_mod_cast h9