import Mathlib

theorem number_theory_191231 : IsGreatest {x | ∀ p : ℕ, Nat.Prime p → p > 5 → x ∣ (p ^ 4 - 1)} 240 := by 
  constructor
  · -- Show 240 is in the set
    intro p hp hp2
    have h2 : p % 2 ≠ 0 := by
      by_contra h
      have : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
    have h3 : p % 3 ≠ 0 := by
      by_contra h
      have : 3 ∣ p := by omega
      have : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    have h5 : p % 5 ≠ 0 := by
      by_contra h
      have : 5 ∣ p := by omega
      have : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
        all_goals omega
      contradiction
    have h16 : (p ^ 4) % 16 = 1 := by
      have h1 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [h, pow_succ, Nat.mul_mod]
    have h3' : (p ^ 4) % 3 = 1 := by
      have h1 : p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h1 with (h | h) <;> norm_num [h, pow_succ, Nat.mul_mod]
    have h5' : (p ^ 4) % 5 = 1 := by
      have h1 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        omega
      rcases h1 with (h | h | h | h) <;> norm_num [h, pow_succ, Nat.mul_mod]
    have : 240 ∣ (p ^ 4 - 1 : ℕ) := by
      omega
    exact_mod_cast this
  · -- Show that there is no greater element in the set
    intro x hx
    have h1 := hx 7 (by norm_num) (by norm_num)
    have h2 := hx 11 (by norm_num) (by norm_num)
    have h3 := hx 13 (by norm_num) (by norm_num)
    have h4 := hx 17 (by norm_num) (by norm_num)
    norm_num at h1 h2 h3 h4
    have h5 : x ∣ 240 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4
    have : x ≤ 240 := by
      exact Nat.le_of_dvd (by norm_num) h5
    linarith